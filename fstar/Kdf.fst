module Kdf

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Evercrypt.Cryptolib

open Hacspec.Cryptolib

open Hacspec.Lib

open Hpke.Errors

type crypto_result_t = (result byte_seq crypto_error_t)

noeq type kdf_t =
| HKDF_SHA256_kdf_t : kdf_t
| HKDF_SHA384_kdf_t : kdf_t
| HKDF_SHA512_kdf_t : kdf_t

type input_key_material_t = byte_seq

type info_t = byte_seq

let kdf_value (kdf_id_0 : kdf_t) : uint16 =
  match kdf_id_0 with
  | HKDF_SHA256_kdf_t -> secret (pub_u16 0x1)
  | HKDF_SHA384_kdf_t -> secret (pub_u16 0x2)
  | HKDF_SHA512_kdf_t -> secret (pub_u16 0x3)

let nh (kdf_id_1 : kdf_t) : uint_size =
  match kdf_id_1 with
  | HKDF_SHA256_kdf_t -> usize 32
  | HKDF_SHA384_kdf_t -> usize 48
  | HKDF_SHA512_kdf_t -> usize 64

let hpke_version_label () : byte_seq =
  array_from_list (
    let l =
      [
        secret (pub_u8 0x48);
        secret (pub_u8 0x50);
        secret (pub_u8 0x4b);
        secret (pub_u8 0x45);
        secret (pub_u8 0x2d);
        secret (pub_u8 0x76);
        secret (pub_u8 0x31)
      ]
    in assert_norm (List.Tot.length l == 7); l)

let hash_for_kdf (alg_2 : kdf_t) : hash_algorithm_t =
  match alg_2 with
  | HKDF_SHA256_kdf_t -> SHA256_hash_algorithm_t
  | HKDF_SHA384_kdf_t -> SHA384_hash_algorithm_t
  | HKDF_SHA512_kdf_t -> SHA512_hash_algorithm_t

let labeled_extract
  (alg_3 : kdf_t)
  (suite_id_4 : byte_seq)
  (salt_5 : byte_seq)
  (label_6 : byte_seq)
  (ikm_7 : input_key_material_t)
  : hpke_byte_seq_result_t =
  match hkdf_extract (hash_for_kdf (alg_3)) (
    seq_concat (
      seq_concat (seq_concat (hpke_version_label ()) (suite_id_4)) (label_6)) (
      ikm_7)) (salt_5) with
  | Ok prk_8 -> Ok (prk_8)
  | Err _ -> Err (CryptoError_hpke_error_t)

let labeled_expand
  (alg_9 : kdf_t)
  (suite_id_10 : byte_seq)
  (prk_11 : byte_seq)
  (label_12 : byte_seq)
  (info_13 : info_t)
  (l_14 : uint_size)
  : hpke_byte_seq_result_t =
  if ((l_14) > ((usize 255) * (nh (alg_9)))) then (
    Err (InvalidParameters_hpke_error_t)) else (
    match hkdf_expand (hash_for_kdf (alg_9)) (prk_11) (
      seq_concat (
        seq_concat (
          seq_concat (
            array_concat (uint16_to_be_bytes (secret (pub_u16 (l_14)))) (
              hpke_version_label ())) (suite_id_10)) (label_12)) (info_13)) (
      l_14) with
    | Ok r_15 -> Ok (r_15)
    | Err _ -> Err (CryptoError_hpke_error_t))

