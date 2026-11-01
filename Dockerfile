# syntax=docker/dockerfile:1
# Charter's server, for Cloudflare Containers. Build for linux/amd64, as wrangler does: docker build --platform linux/amd64 .
# Nothing secret goes in this image. The Worker passes the API key when it starts a container.

FROM debian:12.13-slim AS build
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl gcc libc6-dev binutils zstd \
 && curl -fsSL https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz \
    | tar -xz -C /usr/local/bin \
 && /usr/local/bin/elan-init -y --no-modify-path --default-toolchain none
ENV PATH=/root/.elan/bin:$PATH
WORKDIR /src
# The toolchain gets its own layer, so that a code change does not download it again.
COPY lean-toolchain ./
RUN elan toolchain install "$(cat lean-toolchain)" && elan default "$(cat lean-toolchain)"
COPY . .
RUN lake build charter-server && strip .lake/build/bin/charter-server

FROM debian:12.13-slim
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl \
 && rm -rf /var/lib/apt/lists/* /var/cache/apt/* /usr/share/doc/* /usr/share/man/* \
 && useradd --create-home --uid 1000 charter \
 && install -d -o charter -g charter /data
COPY --from=build /src/.lake/build/bin/charter-server /app/charter-server
COPY --from=build /src/web /app/web
COPY --from=build /src/packs /app/packs
COPY --from=build /src/Server/formalizer.md /src/Server/describer.md /src/Server/player_rules.md /app/Server/
ENV PORT=8080 CHARTER_BIND=0.0.0.0 CHARTER_ROOT=/app CHARTER_DATA=/data/games
# In this stage only, so that a new commit does not build the Lean code again.
ARG CHARTER_COMMIT=unknown
ENV CHARTER_COMMIT=$CHARTER_COMMIT
USER charter
EXPOSE 8080
ENTRYPOINT ["/app/charter-server"]
