module Aead

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Evercrypt.Cryptolib

open Hacspec.Cryptolib

open Hacspec.Lib

open Hpke.Errors

type crypto_result_t = (result byte_seq crypto_error_t)

type aead_alg_result_t = (result aead_algorithm_t hpke_error_t)

noeq type aead_t =
| AES_128_GCM_aead_t : aead_t
| AES_256_GCM_aead_t : aead_t
| ChaCha20Poly1305_aead_t : aead_t
| Export_only_aead_t : aead_t

let nk (aead_id_0 : aead_t) : uint_size =
  match aead_id_0 with
  | AES_128_GCM_aead_t -> usize 16
  | AES_256_GCM_aead_t -> usize 32
  | ChaCha20Poly1305_aead_t -> usize 32
  | Export_only_aead_t -> usize 0

let nt (aead_id_1 : aead_t) : uint_size =
  match aead_id_1 with
  | AES_128_GCM_aead_t -> usize 16
  | AES_256_GCM_aead_t -> usize 16
  | ChaCha20Poly1305_aead_t -> usize 16
  | Export_only_aead_t -> usize 0

let nn (aead_id_2 : aead_t) : uint_size =
  match aead_id_2 with
  | AES_128_GCM_aead_t -> usize 12
  | AES_256_GCM_aead_t -> usize 12
  | ChaCha20Poly1305_aead_t -> usize 12
  | Export_only_aead_t -> usize 0

type key_t = byte_seq

type nonce_t = byte_seq

let alg_for_aead (aead_id_3 : aead_t) : aead_alg_result_t =
  match aead_id_3 with
  | AES_128_GCM_aead_t -> Ok (Aes128Gcm_aead_algorithm_t)
  | AES_256_GCM_aead_t -> Ok (Aes256Gcm_aead_algorithm_t)
  | ChaCha20Poly1305_aead_t -> Ok (Chacha20Poly1305_aead_algorithm_t)
  | Export_only_aead_t -> Err (UnsupportedAlgorithm_hpke_error_t)

let aead_seal
  (aead_id_4 : aead_t)
  (key_5 : key_t)
  (nonce_6 : nonce_t)
  (aad_7 : seq uint8)
  (pt_8 : seq uint8)
  : hpke_byte_seq_result_t =
  match (alg_for_aead (aead_id_4)) with
  | Err x -> Err x
  | Ok  algorithm_9 : aead_algorithm_t ->
    match aead_encrypt (algorithm_9) (key_5) (nonce_6) (pt_8) (aad_7) with
    | Ok ct_10 -> Ok (ct_10)
    | Err _ -> Err (CryptoError_hpke_error_t)

let aead_open
  (aead_id_11 : aead_t)
  (key_12 : key_t)
  (nonce_13 : nonce_t)
  (aad_14 : byte_seq)
  (ct_15 : byte_seq)
  : hpke_byte_seq_result_t =
  match (alg_for_aead (aead_id_11)) with
  | Err x -> Err x
  | Ok  algorithm_16 : aead_algorithm_t ->
    match aead_decrypt (algorithm_16) (key_12) (nonce_13) (ct_15) (aad_14) with
    | Ok pt_17 -> Ok (pt_17)
    | Err _ -> Err (CryptoError_hpke_error_t)

