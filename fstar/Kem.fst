module Kem

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Evercrypt.Cryptolib

open Hacspec.Cryptolib

open Hacspec.Lib

open Hpke.Kdf

open Hpke.Errors

type crypto_result_t = (result byte_seq crypto_error_t)

noeq type kem_t =
| DHKEM_P256_HKDF_SHA256_kem_t : kem_t
| DHKEM_P384_HKDF_SHA384_kem_t : kem_t
| DHKEM_P521_HKDF_SHA512_kem_t : kem_t
| DHKEM_X25519_HKDF_SHA256_kem_t : kem_t
| DHKEM_X448_HKDF_SHA512_kem_t : kem_t

let kem_value (kem_id_0 : kem_t) : uint16 =
  match kem_id_0 with
  | DHKEM_P256_HKDF_SHA256_kem_t -> secret (pub_u16 0x10)
  | DHKEM_P384_HKDF_SHA384_kem_t -> secret (pub_u16 0x11)
  | DHKEM_P521_HKDF_SHA512_kem_t -> secret (pub_u16 0x12)
  | DHKEM_X25519_HKDF_SHA256_kem_t -> secret (pub_u16 0x20)
  | DHKEM_X448_HKDF_SHA512_kem_t -> secret (pub_u16 0x21)

let kdf_for_kem (kem_id_1 : kem_t) : kdf_t =
  match kem_id_1 with
  | DHKEM_P256_HKDF_SHA256_kem_t -> HKDF_SHA256_kdf_t
  | DHKEM_P384_HKDF_SHA384_kem_t -> HKDF_SHA384_kdf_t
  | DHKEM_P521_HKDF_SHA512_kem_t -> HKDF_SHA512_kdf_t
  | DHKEM_X25519_HKDF_SHA256_kem_t -> HKDF_SHA256_kdf_t
  | DHKEM_X448_HKDF_SHA512_kem_t -> HKDF_SHA512_kdf_t

let kem_to_named_group (alg_2 : kem_t) : named_group_t =
  match alg_2 with
  | DHKEM_P256_HKDF_SHA256_kem_t -> Secp256r1_named_group_t
  | DHKEM_P384_HKDF_SHA384_kem_t -> Secp384r1_named_group_t
  | DHKEM_P521_HKDF_SHA512_kem_t -> Secp521r1_named_group_t
  | DHKEM_X25519_HKDF_SHA256_kem_t -> X25519_named_group_t
  | DHKEM_X448_HKDF_SHA512_kem_t -> X448_named_group_t

let nsecret (kem_id_3 : kem_t) : uint_size =
  match kem_id_3 with
  | DHKEM_P256_HKDF_SHA256_kem_t -> usize 32
  | DHKEM_P384_HKDF_SHA384_kem_t -> usize 48
  | DHKEM_P521_HKDF_SHA512_kem_t -> usize 64
  | DHKEM_X25519_HKDF_SHA256_kem_t -> usize 32
  | DHKEM_X448_HKDF_SHA512_kem_t -> usize 64

let nenc (kem_id_4 : kem_t) : uint_size =
  match kem_id_4 with
  | DHKEM_P256_HKDF_SHA256_kem_t -> usize 65
  | DHKEM_P384_HKDF_SHA384_kem_t -> usize 97
  | DHKEM_P521_HKDF_SHA512_kem_t -> usize 133
  | DHKEM_X25519_HKDF_SHA256_kem_t -> usize 32
  | DHKEM_X448_HKDF_SHA512_kem_t -> usize 56

let nsk (kem_id_5 : kem_t) : uint_size =
  match kem_id_5 with
  | DHKEM_P256_HKDF_SHA256_kem_t -> usize 32
  | DHKEM_P384_HKDF_SHA384_kem_t -> usize 48
  | DHKEM_P521_HKDF_SHA512_kem_t -> usize 66
  | DHKEM_X25519_HKDF_SHA256_kem_t -> usize 32
  | DHKEM_X448_HKDF_SHA512_kem_t -> usize 56

let npk (kem_id_6 : kem_t) : uint_size =
  match kem_id_6 with
  | DHKEM_P256_HKDF_SHA256_kem_t -> usize 65
  | DHKEM_P384_HKDF_SHA384_kem_t -> usize 97
  | DHKEM_P521_HKDF_SHA512_kem_t -> usize 133
  | DHKEM_X25519_HKDF_SHA256_kem_t -> usize 32
  | DHKEM_X448_HKDF_SHA512_kem_t -> usize 56

let ndh (kem_id_7 : kem_t) : uint_size =
  match kem_id_7 with
  | DHKEM_P256_HKDF_SHA256_kem_t -> usize 32
  | DHKEM_P384_HKDF_SHA384_kem_t -> usize 48
  | DHKEM_P521_HKDF_SHA512_kem_t -> usize 66
  | DHKEM_X25519_HKDF_SHA256_kem_t -> usize 32
  | DHKEM_X448_HKDF_SHA512_kem_t -> usize 56

type private_key_t = byte_seq

type public_key_t = byte_seq

type key_pair_t = (private_key_t & public_key_t)

type shared_secret_t = byte_seq

type serialized_public_key_t = byte_seq

type randomness_t = byte_seq

type encap_result_t = (
  result (shared_secret_t & serialized_public_key_t) hpke_error_t)

let dkp_prk_label () : byte_seq =
  array_from_list (
    let l =
      [
        secret (pub_u8 0x64);
        secret (pub_u8 0x6b);
        secret (pub_u8 0x70);
        secret (pub_u8 0x5f);
        secret (pub_u8 0x70);
        secret (pub_u8 0x72);
        secret (pub_u8 0x6b)
      ]
    in assert_norm (List.Tot.length l == 7); l)

let eae_prk_label () : byte_seq =
  array_from_list (
    let l =
      [
        secret (pub_u8 0x65);
        secret (pub_u8 0x61);
        secret (pub_u8 0x65);
        secret (pub_u8 0x5f);
        secret (pub_u8 0x70);
        secret (pub_u8 0x72);
        secret (pub_u8 0x6b)
      ]
    in assert_norm (List.Tot.length l == 7); l)

let sk_label () : byte_seq =
  array_from_list (
    let l =
      [secret (pub_u8 0x73); secret (pub_u8 0x6b)]
    in assert_norm (List.Tot.length l == 2); l)

let candidate_label () : byte_seq =
  array_from_list (
    let l =
      [
        secret (pub_u8 0x63);
        secret (pub_u8 0x61);
        secret (pub_u8 0x6e);
        secret (pub_u8 0x64);
        secret (pub_u8 0x69);
        secret (pub_u8 0x64);
        secret (pub_u8 0x61);
        secret (pub_u8 0x74);
        secret (pub_u8 0x65)
      ]
    in assert_norm (List.Tot.length l == 9); l)

let shared_secret_label () : byte_seq =
  array_from_list (
    let l =
      [
        secret (pub_u8 0x73);
        secret (pub_u8 0x68);
        secret (pub_u8 0x61);
        secret (pub_u8 0x72);
        secret (pub_u8 0x65);
        secret (pub_u8 0x64);
        secret (pub_u8 0x5f);
        secret (pub_u8 0x73);
        secret (pub_u8 0x65);
        secret (pub_u8 0x63);
        secret (pub_u8 0x72);
        secret (pub_u8 0x65);
        secret (pub_u8 0x74)
      ]
    in assert_norm (List.Tot.length l == 13); l)

let empty () : byte_seq =
  seq_new_ (secret (pub_u8 0x0)) (usize 0)

let suite_id (alg_8 : kem_t) : byte_seq =
  seq_concat (
    array_from_list (
      let l =
        [secret (pub_u8 0x4b); secret (pub_u8 0x45); secret (pub_u8 0x4d)]
      in assert_norm (List.Tot.length l == 3); l)) (
    uint16_to_be_bytes (kem_value (alg_8)))

let shared_secret_from_dh (alg_9 : kem_t) (secret_10 : byte_seq) : byte_seq =
  match alg_9 with
  | DHKEM_P256_HKDF_SHA256_kem_t -> seq_into_slice (secret_10) (usize 0) (
    ndh (alg_9))
  | DHKEM_P384_HKDF_SHA384_kem_t -> seq_into_slice (secret_10) (usize 0) (
    ndh (alg_9))
  | DHKEM_P521_HKDF_SHA512_kem_t -> seq_into_slice (secret_10) (usize 0) (
    ndh (alg_9))
  | DHKEM_X25519_HKDF_SHA256_kem_t -> secret_10
  | DHKEM_X448_HKDF_SHA512_kem_t -> secret_10

let dh
  (alg_11 : kem_t)
  (sk_12 : private_key_t)
  (pk_13 : public_key_t)
  : (result shared_secret_t hpke_error_t) =
  match ecdh (kem_to_named_group (alg_11)) (sk_12) (pk_13) with
  | Ok secret_14 -> Ok (shared_secret_from_dh (alg_11) (secret_14))
  | Err _ -> Err (ValidationError_hpke_error_t)

let pk
  (alg_15 : kem_t)
  (sk_16 : private_key_t)
  : (result public_key_t hpke_error_t) =
  match secret_to_public (kem_to_named_group (alg_15)) (sk_16) with
  | Ok pk_17 -> Ok (pk_17)
  | Err _ -> Err (ValidationError_hpke_error_t)

let nist_curve_to_uncompressed (pk_18 : public_key_t) : public_key_t =
  let out_19 : seq uint8 =
    seq_new_ (secret (pub_u8 0x0)) (usize 1)
  in
  let out_19 =
    seq_upd out_19 (usize 0) (secret (pub_u8 0x4))
  in
  seq_concat (out_19) (pk_18)

let serialize_public_key
  (alg_20 : kem_t)
  (pk_21 : public_key_t)
  : public_key_t =
  match alg_20 with
  | DHKEM_P256_HKDF_SHA256_kem_t -> nist_curve_to_uncompressed (pk_21)
  | DHKEM_P384_HKDF_SHA384_kem_t -> nist_curve_to_uncompressed (pk_21)
  | DHKEM_P521_HKDF_SHA512_kem_t -> nist_curve_to_uncompressed (pk_21)
  | DHKEM_X25519_HKDF_SHA256_kem_t -> seq_clone (pk_21)
  | DHKEM_X448_HKDF_SHA512_kem_t -> seq_clone (pk_21)

let nist_curve_from_uncompressed
  (alg_22 : kem_t)
  (pk_23 : public_key_t)
  : hpke_byte_seq_result_t =
  match parse_public_key (kem_to_named_group (alg_22)) (pk_23) with
  | Ok pk_24 -> Ok (pk_24)
  | Err _ -> Err (DeserializeError_hpke_error_t)

let deserialize_public_key
  (alg_25 : kem_t)
  (enc_26 : byte_seq)
  : hpke_byte_seq_result_t =
  match alg_25 with
  | DHKEM_P256_HKDF_SHA256_kem_t -> nist_curve_from_uncompressed (alg_25) (
    enc_26)
  | DHKEM_P384_HKDF_SHA384_kem_t -> nist_curve_from_uncompressed (alg_25) (
    enc_26)
  | DHKEM_P521_HKDF_SHA512_kem_t -> nist_curve_from_uncompressed (alg_25) (
    enc_26)
  | DHKEM_X25519_HKDF_SHA256_kem_t -> Ok (seq_clone (enc_26))
  | DHKEM_X448_HKDF_SHA512_kem_t -> Ok (seq_clone (enc_26))

let extract_and_expand
  (alg_27 : kem_t)
  (suite_id_28 : byte_seq)
  (dh_29 : shared_secret_t)
  (kem_context_30 : byte_seq)
  : hpke_byte_seq_result_t =
  let kdf_31 : kdf_t =
    kdf_for_kem (alg_27)
  in
  match (
    labeled_extract (kdf_31) (suite_id_28) (empty ()) (eae_prk_label ()) (
      dh_29)) with
  | Err x -> Err x
  | Ok  eae_prk_32 : seq uint8 ->
    labeled_expand (kdf_31) (suite_id_28) (eae_prk_32) (
      shared_secret_label ()) (kem_context_30) (nsecret (alg_27))

let iint2_osp (counter_33 : uint_size) : byte_seq =
  let bytes_34 : seq uint8 =
    seq_new_ (secret (pub_u8 0x0)) (usize 1)
  in
  let bytes_34 =
    seq_upd bytes_34 (usize 0) (secret (pub_u8 (counter_33)))
  in
  bytes_34

let derive_key_pair_x
  (alg_35 : kem_t)
  (ikm_36 : input_key_material_t)
  : (result key_pair_t hpke_error_t) =
  let suite_id_37 : seq uint8 =
    suite_id (alg_35)
  in
  let kdf_38 : kdf_t =
    kdf_for_kem (alg_35)
  in
  match (
    labeled_extract (kdf_38) (suite_id_37) (empty ()) (dkp_prk_label ()) (
      ikm_36)) with
  | Err x -> Err x
  | Ok  dkp_prk_39 : seq uint8 ->
    match (
      labeled_expand (kdf_38) (suite_id_37) (dkp_prk_39) (sk_label ()) (
        empty ()) (nsk (alg_35))) with
    | Err x -> Err x
    | Ok  sk_40 : seq uint8 ->
      match secret_to_public (kem_to_named_group (alg_35)) (sk_40) with
      | Ok pk_41 -> Ok ((sk_40, seq_from_seq (pk_41)))
      | Err _ -> Err (CryptoError_hpke_error_t)

let derive_key_pair
  (alg_42 : kem_t)
  (ikm_43 : input_key_material_t)
  : (result key_pair_t hpke_error_t) =
  let suite_id_44 : seq uint8 =
    suite_id (alg_42)
  in
  let kdf_45 : kdf_t =
    kdf_for_kem (alg_42)
  in
  match (
    labeled_extract (kdf_45) (suite_id_44) (empty ()) (dkp_prk_label ()) (
      ikm_43)) with
  | Err x -> Err x
  | Ok  dkp_prk_46 : seq uint8 ->
    let named_group_47 : named_group_t =
      kem_to_named_group (alg_42)
    in
    let sk_48 : seq uint8 =
      seq_new_ (secret (pub_u8 0x0)) (usize 0)
    in
    match (
      if ((alg_42) = (DHKEM_X25519_HKDF_SHA256_kem_t)) || (
        (alg_42) = (DHKEM_X448_HKDF_SHA512_kem_t)) then begin
        match (
          labeled_expand (kdf_45) (suite_id_44) (dkp_prk_46) (sk_label ()) (
            empty ()) (usize 32)) with
        | Err x -> Err x
        | Ok  sk_48 ->
          Ok ((sk_48))
      end else begin
        let bitmask_49 : uint8 =
          secret (pub_u8 0xff)
        in
        let (bitmask_49) =
          if (alg_42) = (DHKEM_P521_HKDF_SHA512_kem_t) then begin
            let bitmask_49 =
              secret (pub_u8 0x1)
            in
            (bitmask_49)
          end else begin (bitmask_49)
          end
        in
        match (
          foldi_result (usize 0) (usize 256) (fun counter_50 (sk_48) ->
            match (
              if (seq_len (sk_48)) = (usize 0) then begin
                match (
                  labeled_expand (kdf_45) (suite_id_44) (dkp_prk_46) (
                    candidate_label ()) (iint2_osp (counter_50)) (
                    usize 32)) with
                | Err x -> Err x
                | Ok  bytes_51 : seq uint8 ->
                  let bytes_51 =
                    seq_upd bytes_51 (usize 0) (
                      (seq_index (bytes_51) (usize 0)) &. (bitmask_49))
                  in
                  let (sk_48) =
                    if valid_private_key (named_group_47) (bytes_51) then begin
                      let sk_48 =
                        bytes_51
                      in
                      (sk_48)
                    end else begin (sk_48)
                    end
                  in
                  Ok ((sk_48))
              end else begin Ok ((sk_48))
              end) with
            | Err x -> Err x
            | Ok  (sk_48) ->
              Ok ((sk_48)))
          (sk_48)) with
        | Err x -> Err x
        | Ok  (sk_48) ->
          Ok ((sk_48))
      end) with
    | Err x -> Err x
    | Ok  (sk_48) ->
      if ((seq_len (sk_48)) = (usize 0)) then (
        Err (DeriveKeyPairError_hpke_error_t)) else (
        match secret_to_public (named_group_47) (sk_48) with
        | Ok pk_52 -> Ok ((sk_48, seq_from_seq (pk_52)))
        | Err _ -> Err (CryptoError_hpke_error_t))

let generate_key_pair
  (alg_53 : kem_t)
  (randomness_54 : randomness_t)
  : (result key_pair_t hpke_error_t) =
  derive_key_pair (alg_53) (randomness_54)

let encap
  (alg_55 : kem_t)
  (pk_r_56 : public_key_t)
  (randomness_57 : randomness_t)
  : encap_result_t =
  match (generate_key_pair (alg_55) (randomness_57)) with
  | Err x -> Err x
  | Ok  (sk_e_58, pk_e_59) : key_pair_t ->
    match (dh (alg_55) (sk_e_58) (pk_r_56)) with
    | Err x -> Err x
    | Ok  dh_60 : shared_secret_t ->
      let enc_61 : seq uint8 =
        serialize_public_key (alg_55) (pk_e_59)
      in
      let pk_rm_62 : seq uint8 =
        serialize_public_key (alg_55) (pk_r_56)
      in
      let kem_context_63 : seq uint8 =
        seq_concat (enc_61) (pk_rm_62)
      in
      match (
        extract_and_expand (alg_55) (suite_id (alg_55)) (dh_60) (
          kem_context_63)) with
      | Err x -> Err x
      | Ok  shared_secret_64 : seq uint8 ->
        Ok ((shared_secret_64, enc_61))

let decap
  (alg_65 : kem_t)
  (enc_66 : byte_seq)
  (sk_r_67 : private_key_t)
  : (result shared_secret_t hpke_error_t) =
  match (deserialize_public_key (alg_65) (enc_66)) with
  | Err x -> Err x
  | Ok  pk_e_68 : seq uint8 ->
    match (dh (alg_65) (sk_r_67) (pk_e_68)) with
    | Err x -> Err x
    | Ok  dh_69 : shared_secret_t ->
      match (pk (alg_65) (sk_r_67)) with
      | Err x -> Err x
      | Ok  pk_r_70 : public_key_t ->
        let pk_rm_71 : seq uint8 =
          serialize_public_key (alg_65) (pk_r_70)
        in
        let kem_context_72 : seq uint8 =
          seq_concat (enc_66) (pk_rm_71)
        in
        extract_and_expand (alg_65) (suite_id (alg_65)) (dh_69) (kem_context_72)

let auth_encap
  (alg_73 : kem_t)
  (pk_r_74 : public_key_t)
  (sk_s_75 : private_key_t)
  (randomness_76 : randomness_t)
  : encap_result_t =
  match (generate_key_pair (alg_73) (randomness_76)) with
  | Err x -> Err x
  | Ok  (sk_e_77, pk_e_78) : key_pair_t ->
    match (dh (alg_73) (sk_e_77) (pk_r_74)) with
    | Err x -> Err x
    | Ok  dh_e_79 : shared_secret_t ->
      match (dh (alg_73) (sk_s_75) (pk_r_74)) with
      | Err x -> Err x
      | Ok  dh_s_80 : shared_secret_t ->
        let dh_81 : seq uint8 =
          seq_concat_owned (dh_e_79) (dh_s_80)
        in
        let enc_82 : seq uint8 =
          serialize_public_key (alg_73) (pk_e_78)
        in
        let pk_rm_83 : seq uint8 =
          serialize_public_key (alg_73) (pk_r_74)
        in
        match (pk (alg_73) (sk_s_75)) with
        | Err x -> Err x
        | Ok  pk_s_84 : public_key_t ->
          let pk_sm_85 : seq uint8 =
            serialize_public_key (alg_73) (pk_s_84)
          in
          let kem_context_86 : seq uint8 =
            seq_concat_owned (seq_concat (enc_82) (pk_rm_83)) (pk_sm_85)
          in
          match (
            extract_and_expand (alg_73) (suite_id (alg_73)) (dh_81) (
              kem_context_86)) with
          | Err x -> Err x
          | Ok  shared_secret_87 : seq uint8 ->
            Ok ((shared_secret_87, enc_82))

let auth_decap
  (alg_88 : kem_t)
  (enc_89 : byte_seq)
  (sk_r_90 : private_key_t)
  (pk_s_91 : public_key_t)
  : (result shared_secret_t hpke_error_t) =
  match (deserialize_public_key (alg_88) (enc_89)) with
  | Err x -> Err x
  | Ok  pk_e_92 : seq uint8 ->
    match (dh (alg_88) (sk_r_90) (pk_e_92)) with
    | Err x -> Err x
    | Ok  dh_e_93 : shared_secret_t ->
      match (dh (alg_88) (sk_r_90) (pk_s_91)) with
      | Err x -> Err x
      | Ok  dh_s_94 : shared_secret_t ->
        let dh_95 : seq uint8 =
          seq_concat_owned (dh_e_93) (dh_s_94)
        in
        match (pk (alg_88) (sk_r_90)) with
        | Err x -> Err x
        | Ok  pk_r_96 : public_key_t ->
          let pk_rm_97 : seq uint8 =
            serialize_public_key (alg_88) (pk_r_96)
          in
          let pk_sm_98 : seq uint8 =
            serialize_public_key (alg_88) (pk_s_91)
          in
          let kem_context_99 : seq uint8 =
            seq_concat_owned (seq_concat (enc_89) (pk_rm_97)) (pk_sm_98)
          in
          extract_and_expand (alg_88) (suite_id (alg_88)) (dh_95) (
            kem_context_99)

