FROM python:3.12.10-slim-bookworm AS base
RUN apt-get update \
    && apt-get install -y --no-install-recommends build-essential ca-certificates curl elan git \
    && rm -rf /var/lib/apt/lists/*
ENV ELAN_HOME=/opt/elan
WORKDIR /repo
COPY packages/KATLean/lean-toolchain /repo/lean-toolchain
RUN elan toolchain install "$(cat lean-toolchain)"
COPY scripts/verify-release.sh scripts/verify-release.sh
COPY docker/link-locked-dependencies.py docker/link-locked-dependencies.py

FROM base AS katlean
COPY packages/KATLean/ packages/KATLean/
COPY docker/fetch-locked-dependencies.py docker/fetch-locked-dependencies.py
RUN python3 docker/fetch-locked-dependencies.py packages/KATLean
RUN lake -d packages/KATLean -v build proofwidgets:release \
    && lake -d packages/KATLean build
CMD ["bash", "scripts/verify-release.sh", "KATLean"]

FROM katlean AS netkatlean
COPY packages/NetKATLean/ packages/NetKATLean/
RUN python3 docker/link-locked-dependencies.py packages/NetKATLean \
    && lake -d packages/NetKATLean build
CMD ["bash", "scripts/verify-release.sh", "NetKATLean"]

FROM netkatlean AS dynetkatlean
COPY packages/DyNetKATLean/ packages/DyNetKATLean/
RUN python3 docker/link-locked-dependencies.py packages/DyNetKATLean \
    && lake -d packages/DyNetKATLean build
CMD ["bash", "scripts/verify-release.sh", "DyNetKATLean"]

FROM dynetkatlean AS integration
COPY docker/requirements-test.txt docker/requirements-test.txt
RUN python3 -m pip install --no-cache-dir --no-deps -r docker/requirements-test.txt
COPY lean/ lean/
COPY python/ python/
COPY scripts/verify.sh scripts/verify-package-independence.py scripts/katch_replay.py scripts/
RUN python3 docker/link-locked-dependencies.py lean \
    && lake -d lean build DyNetKAT dynetkat +DyNetKAT.Experimental +DyNetKAT.NetKAT.Legacy
CMD ["bash", "scripts/verify-release.sh"]
