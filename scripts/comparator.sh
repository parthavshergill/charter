#!/bin/bash
# Run Lean's Comparator on Charter's proofs. Exit code 0 means accepted, as `lake comparator --help` says.
#
#   bash scripts/comparator.sh              the normal run, inside the bubblewrap sandbox.
#   bash scripts/comparator.sh --paranoid   adds the other checkers that ship with Lean.
#
# Comparator's sandbox needs Linux, so this runs in a Docker container with bubblewrap. The container is
# privileged because bubblewrap needs that inside Docker. The container gets a copy of the Lean files only.
#
# After you add a theorem:
#   python3 scripts/comparator_challenge.py write
#   bash scripts/comparator.sh
#
# The first run needs about 5 GB free. It leaves a small image, and a volume that holds Lean and the build
# results, so the next run is faster. To remove them:
#   docker volume rm charter-comparator && docker rmi charter-comparator
set -euo pipefail
cd "$(dirname "$0")/.."

python3 scripts/comparator_challenge.py check
bash scripts/statement_lock.sh check

docker build --quiet --tag charter-comparator - < scripts/comparator.Dockerfile
docker volume create charter-comparator > /dev/null

echo "Checking commit $(git rev-parse --short HEAD). Uncommitted files: $(git status --porcelain | wc -l | tr -d ' ')."

# macOS tar must not add its own metadata to the files.
COPYFILE_DISABLE=1 tar --exclude .lake -cf - \
    lakefile.toml lake-manifest.json lean-toolchain comparator.json Charter.lean Charter Comparator packages forks \
    Server/SExp.lean Server/Rules.lean Server/ResourcesNamed.lean Server/ParserProof.lean Server/ParserFacts.lean \
  | docker run --rm -i --privileged --name charter-comparator-run \
      --cpuset-cpus "${COMPARATOR_CPUSET:-0-7}" --memory "${COMPARATOR_MEMORY:-14g}" \
      --volume charter-comparator:/work charter-comparator bash -c '
set -euo pipefail
mkdir -p /work/charter
cd /work/charter
# Keep only the build results, so that a deleted file does not linger in the copy.
find . -mindepth 1 -maxdepth 1 ! -name .lake -exec rm -rf {} +
tar -xf - --warning=no-unknown-keyword
# The fork has a lakefile.lean, so Lake creates this empty directory when it loads the project. The
# sandbox can write only to the root .lake, so the directory must be there first.
mkdir -p forks/leansqlite/.lake
# The Island needs HexGrid, so the sandbox builds it too. Its build results must go under the root .lake.
mkdir -p .lake/hexgrid
ln -s ../../.lake/hexgrid packages/lean-hexgrid/.lake
test -x /work/elan/bin/elan || elan-init -y --no-modify-path --default-toolchain none
elan toolchain install "$(cat lean-toolchain)"
# The real binaries, not the elan wrappers: the sandbox removes what the wrappers need.
export PATH="$(lean --print-prefix)/bin:$PATH"
lake --version
bwrap --version
SECONDS=0
status=0
lake comparator "$@" || status=$?
echo "lake comparator $* exited with $status after $SECONDS seconds."
echo "Build results: $(du -sh .lake | cut -f1)."
exit "$status"
' -- "$@"
