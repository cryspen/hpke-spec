#/bin/bash

set -e

cargo doc --no-deps \
    -p hpke \
    -p hacspec-chacha20poly1305 \
    -p hacspec-hkdf \
    -p hacspec-p256 \
    -p hacspec-aes128-gcm \
    -p hacspec-curve25519
