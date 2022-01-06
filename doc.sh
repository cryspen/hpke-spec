#/bin/bash

set -e

cargo doc --no-deps \
    -p hpke_kem \
    -p hpke_kdf \
    -p hpke_aead \
    -p hpke_errors \
    -p hpke \
    -p hacspec-chacha20poly1305 \
    -p hacspec-hkdf \
    -p hacspec-p256 \
    -p hacspec-aes128-gcm \
    -p hacspec-curve25519
