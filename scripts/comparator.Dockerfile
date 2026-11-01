# The Linux system that scripts/comparator.sh runs Comparator in. It holds no project files.
# Lean itself goes in the volume at run time. An image layer of that size takes about 10 GB to build.
FROM debian:12.13-slim
ENV ELAN_HOME=/work/elan PATH=/work/elan/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
RUN apt-get update \
 && apt-get install -y --no-install-recommends bubblewrap ca-certificates curl git zstd \
 && rm -rf /var/lib/apt/lists/* /var/cache/apt/* /usr/share/doc/* /usr/share/man/* \
 && mkdir -p /run/user \
 && curl -fsSL "https://github.com/leanprover/elan/releases/download/v4.2.4/elan-$(uname -m)-unknown-linux-gnu.tar.gz" \
    | tar -xz -C /usr/local/bin
