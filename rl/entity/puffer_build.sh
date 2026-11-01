#!/usr/bin/env bash
# Compile the entity encoder into PufferLib: copy the .cu, write its layout header, add the hook to src/ocean.cu.
# Usage: bash puffer_build.sh PUFFER_DIR OCEAN_DIR LAYOUT_JSON. The last line printed is the extra nvcc flags.
# CHARTER_ENTITY_DIM (default 32) sets the numbers per row, and CHARTER_POINTER=1 adds the pointer decoder, and 2 also scores bank trades;
# modal_app.py sets both from --meta-extra's entity_dim and pointer.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PUFFER="$1"; OCEAN="$2"; LAYOUT="$3"
cp "$HERE/charter_entity.cu" "$OCEAN/"
python3 "$HERE/gen_layout.py" "$LAYOUT" "$OCEAN/charter_entity_layout.h"
python3 "$HERE/apply_hook.py" "$PUFFER"
echo "-DPUFFER_CHARTER_ENTITY -DCE_ENTITY_DIM=${CHARTER_ENTITY_DIM:-32}$([ "${CHARTER_POINTER:-0}" -ge 1 ] && echo " -DCE_POINTER")$([ "${CHARTER_POINTER:-0}" = 2 ] && echo " -DCE_POINTER_BANK")"
