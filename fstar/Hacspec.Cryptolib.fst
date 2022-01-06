module Hacspec.Cryptolib

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

open Hacspec.Aes

open Hacspec.Aes128.Gcm

open Hacspec.Chacha20

open Hacspec.Chacha20poly1305

open Hacspec.Curve25519

open Hacspec.Ecdsa.P256.Sha256

open Hacspec.Gf128

open Hacspec.Hkdf

open Hacspec.Hmac

open Hacspec.P256

open Hacspec.Poly1305

open Hacspec.Sha256

type crypto_error_t = pub_uint8

type key_t = byte_seq

type psk_t = key_t

type digest_t = byte_seq

type mac_key_t = byte_seq

type hmac_t = byte_seq

type signature_key_t = byte_seq

type verification_key_t = byte_seq

type signature_t = byte_seq

type aead_key_t = byte_seq

type aead_iv_t = byte_seq

type aead_key_iv_t = (aead_key_t & aead_iv_t)

type entropy_t = byte_seq

type dh_sk_t = byte_seq

type dh_pk_t = byte_seq

type kem_scheme_t = named_group_t

type kem_sk_t = byte_seq

type kem_pk_t = byte_seq

type ec_oid_tag_t = lseq (uint8) (usize 9)

type random32_t = lseq (uint8) (usize 32)

type dh_pk_result_t = (result dh_pk_t crypto_error_t)

type empty_result_t = (result () crypto_error_t)

type crypto_byte_seq_result_t = (result byte_seq crypto_error_t)

type crypto_byte_seq2_result_t = (result (byte_seq & byte_seq) crypto_error_t)

let crypto_error_v : crypto_error_t =
  pub_u8 0x1

let hkdf_error_v : crypto_error_t =
  pub_u8 0x2

let insufficient_entropy_v : crypto_error_t =
  pub_u8 0x3

let invalid_cert_v : crypto_error_t =
  pub_u8 0x4

let mac_failed_v : crypto_error_t =
  pub_u8 0x5

let unsupported_algorithm_v : crypto_error_t =
  pub_u8 0x6

let verify_failed_v : crypto_error_t =
  pub_u8 0x7

noeq type named_group_t =
| X25519_named_group_t : named_group_t
| X448_named_group_t : named_group_t
| Secp256r1_named_group_t : named_group_t
| Secp384r1_named_group_t : named_group_t
| Secp521r1_named_group_t : named_group_t

noeq type hash_algorithm_t =
| SHA256_hash_algorithm_t : hash_algorithm_t
| SHA384_hash_algorithm_t : hash_algorithm_t
| SHA512_hash_algorithm_t : hash_algorithm_t

noeq type aead_algorithm_t =
| Chacha20Poly1305_aead_algorithm_t : aead_algorithm_t
| Aes128Gcm_aead_algorithm_t : aead_algorithm_t
| Aes256Gcm_aead_algorithm_t : aead_algorithm_t

noeq type signature_scheme_t =
| ED25519_signature_scheme_t : signature_scheme_t
| EcdsaSecp256r1Sha256_signature_scheme_t : signature_scheme_t
| RsaPssRsaSha256_signature_scheme_t : signature_scheme_t

let named_group_support (named_group_0 : named_group_t) : empty_result_t =
  match named_group_0 with
  | X25519_named_group_t -> Ok (())
  | Secp256r1_named_group_t -> Ok (())
  | X448_named_group_t -> Err (unsupported_algorithm_v)
  | Secp384r1_named_group_t -> Err (unsupported_algorithm_v)
  | Secp521r1_named_group_t -> Err (unsupported_algorithm_v)

let hash_support (hash_1 : hash_algorithm_t) : empty_result_t =
  match hash_1 with
  | SHA256_hash_algorithm_t -> Ok (())
  | SHA384_hash_algorithm_t -> Err (unsupported_algorithm_v)
  | SHA512_hash_algorithm_t -> Err (unsupported_algorithm_v)

let aead_support (aead_2 : aead_algorithm_t) : empty_result_t =
  match aead_2 with
  | Chacha20Poly1305_aead_algorithm_t -> Ok (())
  | Aes128Gcm_aead_algorithm_t -> Ok (())
  | Aes256Gcm_aead_algorithm_t -> Err (unsupported_algorithm_v)

let signature_support (signature_3 : signature_scheme_t) : empty_result_t =
  match signature_3 with
  | ED25519_signature_scheme_t -> Ok (())
  | EcdsaSecp256r1Sha256_signature_scheme_t -> Ok (())
  | RsaPssRsaSha256_signature_scheme_t -> Err (unsupported_algorithm_v)

let hash_len (ha_4 : hash_algorithm_t) : uint_size =
  match ha_4 with
  | SHA256_hash_algorithm_t -> usize 32
  | SHA384_hash_algorithm_t -> usize 48
  | SHA512_hash_algorithm_t -> usize 64

let hmac_tag_len (ha_5 : hash_algorithm_t) : uint_size =
  match ha_5 with
  | SHA256_hash_algorithm_t -> usize 32
  | SHA384_hash_algorithm_t -> usize 48
  | SHA512_hash_algorithm_t -> usize 64

let ae_key_len (ae_6 : aead_algorithm_t) : uint_size =
  match ae_6 with
  | Chacha20Poly1305_aead_algorithm_t -> usize 32
  | Aes128Gcm_aead_algorithm_t -> usize 16
  | Aes256Gcm_aead_algorithm_t -> usize 16

let ae_iv_len (ae_7 : aead_algorithm_t) : uint_size =
  match ae_7 with
  | Chacha20Poly1305_aead_algorithm_t -> usize 12
  | Aes128Gcm_aead_algorithm_t -> usize 12
  | Aes256Gcm_aead_algorithm_t -> usize 12

let dh_priv_len (gn_8 : named_group_t) : uint_size =
  match gn_8 with
  | X25519_named_group_t -> usize 32
  | X448_named_group_t -> usize 56
  | Secp256r1_named_group_t -> usize 32
  | Secp384r1_named_group_t -> usize 48
  | Secp521r1_named_group_t -> usize 66

let dh_pub_len (gn_9 : named_group_t) : uint_size =
  match gn_9 with
  | X25519_named_group_t -> usize 32
  | X448_named_group_t -> usize 56
  | Secp256r1_named_group_t -> usize 64
  | Secp384r1_named_group_t -> usize 96
  | Secp521r1_named_group_t -> usize 132

let zero_key (ha_10 : hash_algorithm_t) : key_t =
  seq_new_ (secret (pub_u8 0x0)) (usize (hash_len (ha_10)))

let secret_to_public
  (group_name_11 : named_group_t)
  (x_12 : dh_sk_t)
  : dh_pk_result_t =
  match group_name_11 with
  | Secp256r1_named_group_t -> match p256_point_mul_base (
    nat_from_byte_seq_be (0xunknown) (0) (x_12)) with
  | Ok (x_13, y_14) -> Ok (
    seq_concat (nat_to_byte_seq_be (0xunknown) (0) (x_13)) (
      nat_to_byte_seq_be (0xunknown) (0) (y_14)))
  | Err _ -> Err (crypto_error_v)
  | X25519_named_group_t -> Ok (
    seq_from_seq (x25519_secret_to_public (array_from_seq (32) (x_12))))
  | X448_named_group_t -> Err (unsupported_algorithm_v)
  | Secp384r1_named_group_t -> Err (unsupported_algorithm_v)
  | Secp521r1_named_group_t -> Err (unsupported_algorithm_v)

let p256_check_point_len (p_15 : dh_pk_t) : empty_result_t =
  if ((seq_len (p_15)) <> (usize 64)) then (Err (crypto_error_v)) else (Ok (()))

let p256_ecdh (x_16 : dh_sk_t) (y_17 : dh_pk_t) : crypto_byte_seq_result_t =
  match (p256_check_point_len (y_17)) with
  | Err x -> Err x
  | Ok  _ : () ->
    let pk_18 : (p256_field_element_t & p256_field_element_t) =
      (
        nat_from_byte_seq_be (0xunknown) (0) (
          seq_slice_range (y_17) ((usize 0, usize 32))),
        nat_from_byte_seq_be (0xunknown) (0) (
          seq_slice_range (y_17) ((usize 32, usize 64)))
      )
    in
    match p256_point_mul (nat_from_byte_seq_be (0xunknown) (0) (x_16)) (
      pk_18) with
    | Ok (x_19, y_20) -> Ok (
      seq_concat (nat_to_byte_seq_be (0xunknown) (0) (x_19)) (
        nat_to_byte_seq_be (0xunknown) (0) (y_20)))
    | Err _ -> Err (crypto_error_v)

let ecdh
  (group_name_21 : named_group_t)
  (x_22 : dh_sk_t)
  (y_23 : dh_pk_t)
  : crypto_byte_seq_result_t =
  match group_name_21 with
  | Secp256r1_named_group_t -> p256_ecdh (x_22) (y_23)
  | X25519_named_group_t -> Ok (
    seq_from_seq (
      x25519_scalarmult (array_from_seq (32) (x_22)) (
        array_from_seq (32) (y_23))))
  | X448_named_group_t -> Err (unsupported_algorithm_v)
  | Secp384r1_named_group_t -> Err (unsupported_algorithm_v)
  | Secp521r1_named_group_t -> Err (unsupported_algorithm_v)

let valid_p256_private_key (k_24 : byte_seq) : bool =
  let k_element_25 : p256_scalar_t =
    nat_from_byte_seq_be (0xunknown) (0) (k_24)
  in
  let k_element_bytes_26 : seq uint8 =
    nat_to_byte_seq_be (0xunknown) (0) (k_element_25)
  in
  let valid_27 : bool =
    (seq_len (k_element_bytes_26)) = (seq_len (k_24))
  in
  let all_zero_28 : bool =
    true
  in
  let (valid_27, all_zero_28) =
    if valid_27 then begin
      let (valid_27, all_zero_28) =
        foldi (usize 0) (seq_len (k_24)) (fun i_29 (valid_27, all_zero_28) ->
          let (all_zero_28) =
            if not (
              uint8_equal (seq_index (k_24) (i_29)) (
                secret (pub_u8 0x0))) then begin
              let all_zero_28 =
                false
              in
              (all_zero_28)
            end else begin (all_zero_28)
            end
          in
          let (valid_27) =
            if not (
              uint8_equal (seq_index (k_element_bytes_26) (i_29)) (
                seq_index (k_24) (i_29))) then begin
              let valid_27 =
                false
              in
              (valid_27)
            end else begin (valid_27)
            end
          in
          (valid_27, all_zero_28))
        (valid_27, all_zero_28)
      in
      (valid_27, all_zero_28)
    end else begin (valid_27, all_zero_28)
    end
  in
  (valid_27) && (not (all_zero_28))

let valid_private_key
  (named_group_30 : named_group_t)
  (bytes_31 : dh_sk_t)
  : bool =
  match named_group_30 with
  | X25519_named_group_t -> (seq_len (bytes_31)) = (
    dh_priv_len (named_group_30))
  | X448_named_group_t -> (seq_len (bytes_31)) = (dh_priv_len (named_group_30))
  | Secp256r1_named_group_t -> valid_p256_private_key (bytes_31)
  | Secp384r1_named_group_t -> false
  | Secp521r1_named_group_t -> false

let parse_public_key
  (named_group_32 : named_group_t)
  (bytes_33 : dh_pk_t)
  : (result dh_pk_t crypto_error_t) =
  match named_group_32 with
  | X25519_named_group_t -> Ok (seq_clone (bytes_33))
  | X448_named_group_t -> Ok (seq_clone (bytes_33))
  | Secp256r1_named_group_t -> Ok (
    seq_slice (bytes_33) (usize 1) ((seq_len (bytes_33)) - (usize 1)))
  | Secp384r1_named_group_t -> Err (unsupported_algorithm_v)
  | Secp521r1_named_group_t -> Err (unsupported_algorithm_v)

let kem_priv_len (ks_34 : kem_scheme_t) : uint_size =
  dh_priv_len (ks_34)

let kem_pub_len (ks_35 : kem_scheme_t) : uint_size =
  dh_pub_len (ks_35)

let kem_priv_to_pub
  (ks_36 : kem_scheme_t)
  (sk_37 : kem_sk_t)
  : crypto_byte_seq_result_t =
  secret_to_public (ks_36) (sk_37)

let kem_keygen
  (ks_38 : kem_scheme_t)
  (ent_39 : entropy_t)
  : crypto_byte_seq2_result_t =
  let result_40 : (result (byte_seq & byte_seq) crypto_error_t) =
    Err (insufficient_entropy_v)
  in
  match (
    if (seq_len (ent_39)) >= (kem_priv_len (ks_38)) then begin
      let sk_41 : seq uint8 =
        seq_from_seq (
          seq_slice_range (ent_39) ((usize 0, kem_priv_len (ks_38))))
      in
      match (kem_priv_to_pub (ks_38) (sk_41)) with
      | Err x -> Err x
      | Ok  pk_42 : byte_seq ->
        let result_40 =
          Ok ((sk_41, pk_42))
        in
        Ok ((result_40))
    end else begin Ok ((result_40))
    end) with
  | Err x -> Err x
  | Ok  (result_40) ->
    result_40

let kem_encap
  (ks_43 : kem_scheme_t)
  (pk_44 : kem_pk_t)
  (ent_45 : entropy_t)
  : crypto_byte_seq2_result_t =
  match (kem_keygen (ks_43) (ent_45)) with
  | Err x -> Err x
  | Ok  (x_46, gx_47) : (byte_seq & byte_seq) ->
    match (ecdh (ks_43) (x_46) (pk_44)) with
    | Err x -> Err x
    | Ok  gxy_48 : byte_seq ->
      Ok ((gxy_48, gx_47))

let kem_decap
  (ks_49 : kem_scheme_t)
  (ct_50 : byte_seq)
  (sk_51 : kem_sk_t)
  : crypto_byte_seq_result_t =
  match (ecdh (ks_49) (sk_51) (ct_50)) with
  | Err x -> Err x
  | Ok  gxy_52 : byte_seq ->
    Ok (gxy_52)

let hash
  (ha_53 : hash_algorithm_t)
  (payload_54 : byte_seq)
  : crypto_byte_seq_result_t =
  match ha_53 with
  | SHA256_hash_algorithm_t -> Ok (seq_from_seq (sha256 (payload_54)))
  | SHA384_hash_algorithm_t -> Err (unsupported_algorithm_v)
  | SHA512_hash_algorithm_t -> Err (unsupported_algorithm_v)

let hmac_tag
  (ha_55 : hash_algorithm_t)
  (mk_56 : mac_key_t)
  (payload_57 : byte_seq)
  : crypto_byte_seq_result_t =
  match ha_55 with
  | SHA256_hash_algorithm_t -> Ok (seq_from_seq (hmac (mk_56) (payload_57)))
  | SHA384_hash_algorithm_t -> Err (unsupported_algorithm_v)
  | SHA512_hash_algorithm_t -> Err (unsupported_algorithm_v)

let check_tag_len (a_58 : hmac_t) (b_59 : hmac_t) : empty_result_t =
  if ((seq_len (a_58)) = (seq_len (b_59))) then (Ok (())) else (
    Err (mac_failed_v))

let check_bytes (a_60 : uint8) (b_61 : uint8) : empty_result_t =
  if (not (uint8_equal (a_60) (b_61))) then (Err (mac_failed_v)) else (Ok (()))

let hmac_verify
  (ha_62 : hash_algorithm_t)
  (mk_63 : mac_key_t)
  (payload_64 : byte_seq)
  (t_65 : hmac_t)
  : empty_result_t =
  match (hmac_tag (ha_62) (mk_63) (payload_64)) with
  | Err x -> Err x
  | Ok  my_hmac_66 : byte_seq ->
    match (check_tag_len (t_65) (my_hmac_66)) with
    | Err x -> Err x
    | Ok  _ : () ->
      match (
        foldi_result (usize 0) (seq_len (t_65)) (fun i_67 () ->
          match (
            check_bytes (seq_index (my_hmac_66) (i_67)) (
              seq_index (t_65) (i_67))) with
          | Err x -> Err x
          | Ok  _ : () ->
            Ok (()))
        ()) with
      | Err x -> Err x
      | Ok  () ->
        Ok (())

let get_length_length (b_68 : byte_seq) : uint_size =
  if (
    (
      (uint8_declassify (seq_index (b_68) (usize 0))) `shift_right` (
        usize 7)) = (pub_u8 0x1)) then (
    declassify_usize_from_uint8 (
      (seq_index (b_68) (usize 0)) &. (secret (pub_u8 0x7f)))) else (usize 0)

let get_length (b_69 : byte_seq) (len_70 : uint_size) : uint_size =
  (
    v (
      cast U32 PUB (
        declassify_u32_from_uint32 (
          uint32_from_be_bytes (
            array_from_slice (secret (pub_u8 0x0)) (4) (b_69) (usize 0) (
              len_70)))))) `usize_shift_right` (
    ((usize 4) - (len_70)) * (usize 8))

let get_short_length (b_71 : byte_seq) : uint_size =
  declassify_usize_from_uint8 (
    (seq_index (b_71) (usize 0)) &. (secret (pub_u8 0x7f)))

let verification_key_from_cert
  (cert_72 : byte_seq)
  : (result verification_key_t crypto_error_t) =
  let skip_73 : uint_size =
    (
      (usize 2) + (
        get_length_length (
          seq_slice_range (cert_72) ((usize 1, seq_len (cert_72)))))) + (
      usize 1)
  in
  let seq1_len_len_74 : uint_size =
    get_length_length (seq_slice_range (cert_72) ((skip_73, seq_len (cert_72))))
  in
  let skip_75 : uint_size =
    (skip_73) + (usize 1)
  in
  let seq1_len_76 : uint_size =
    get_length (
      seq_slice (cert_72) (skip_75) ((seq_len (cert_72)) - (skip_75))) (
      seq1_len_len_74)
  in
  let seq1_77 : seq uint8 =
    seq_slice_range (cert_72) (
      (
        (skip_75) + (seq1_len_len_74),
        ((skip_75) + (seq1_len_len_74)) + (seq1_len_76)
      ))
  in
  let pk_78 : seq uint8 =
    seq_new_ (secret (pub_u8 0x0)) (usize 0)
  in
  let (seq1_77, pk_78) =
    foldi (usize 0) (seq_len (seq1_77)) (fun _ (seq1_77, pk_78) ->
      let (seq1_77, pk_78) =
        if (seq_len (seq1_77)) > (usize 0) then begin
          let element_type_79 : pub_uint8 =
            uint8_declassify (seq_index (seq1_77) (usize 0))
          in
          let seq1_77 =
            seq_slice (seq1_77) (usize 1) ((seq_len (seq1_77)) - (usize 1))
          in
          let len_len_80 : uint_size =
            get_length_length (seq1_77)
          in
          let len_81 : uint_size =
            get_short_length (seq1_77)
          in
          let seq1_77 =
            seq_slice (seq1_77) (usize 1) ((seq_len (seq1_77)) - (usize 1))
          in
          let (len_81) =
            if (len_len_80) <> (usize 0) then begin
              let len_81 =
                (get_length (seq1_77) (len_len_80)) + (len_len_80)
              in
              (len_81)
            end else begin (len_81)
            end
          in
          let (pk_78) =
            if ((element_type_79) = (pub_u8 0x30)) && (
              (seq_len (pk_78)) = (usize 0)) then begin
              let seq2_82 : seq uint8 =
                seq_slice (seq1_77) (len_len_80) (len_81)
              in
              let element_type_83 : pub_uint8 =
                uint8_declassify (seq_index (seq2_82) (usize 0))
              in
              let seq2_84 : seq uint8 =
                seq_slice (seq2_82) (usize 1) ((seq_len (seq2_82)) - (usize 1))
              in
              let (pk_78) =
                if (element_type_83) = (pub_u8 0x30) then begin
                  let len_len_85 : uint_size =
                    get_length_length (seq2_84)
                  in
                  let (pk_78) =
                    if (len_len_85) = (usize 0) then begin
                      let oid_len_86 : uint_size =
                        get_short_length (seq2_84)
                      in
                      let (pk_78) =
                        if (oid_len_86) >= (usize 9) then begin
                          let expected_87 : seq uint8 =
                            seq_from_seq (
                              array_from_list (
                                let l =
                                  [
                                    secret (pub_u8 0x6);
                                    secret (pub_u8 0x7);
                                    secret (pub_u8 0x2a);
                                    secret (pub_u8 0x86);
                                    secret (pub_u8 0x48);
                                    secret (pub_u8 0xce);
                                    secret (pub_u8 0x3d);
                                    secret (pub_u8 0x2);
                                    secret (pub_u8 0x1)
                                  ]
                                in assert_norm (List.Tot.length l == 9); l))
                          in
                          let oid_88 : seq uint8 =
                            seq_slice (seq2_84) (usize 1) (usize 9)
                          in
                          let ec_pk_oid_89 : bool =
                            true
                          in
                          let (ec_pk_oid_89) =
                            foldi (usize 0) (usize 9) (fun i_90 (ec_pk_oid_89
                              ) ->
                              let oid_byte_equal_91 : bool =
                                (
                                  uint8_declassify (
                                    seq_index (oid_88) (i_90))) = (
                                  uint8_declassify (
                                    seq_index (expected_87) (i_90)))
                              in
                              let ec_pk_oid_89 =
                                (ec_pk_oid_89) && (oid_byte_equal_91)
                              in
                              (ec_pk_oid_89))
                            (ec_pk_oid_89)
                          in
                          let (pk_78) =
                            if ec_pk_oid_89 then begin
                              let bit_string_92 : seq uint8 =
                                seq_slice (seq2_84) ((oid_len_86) + (usize 1)) (
                                  ((seq_len (seq2_84)) - (oid_len_86)) - (
                                    usize 1))
                              in
                              let (pk_78) =
                                if (
                                  uint8_declassify (
                                    seq_index (bit_string_92) (usize 0))) = (
                                  pub_u8 0x3) then begin
                                  let pk_len_93 : uint_size =
                                    declassify_usize_from_uint8 (
                                      seq_index (bit_string_92) (usize 1))
                                  in
                                  let zeroes_94 : uint_size =
                                    declassify_usize_from_uint8 (
                                      seq_index (bit_string_92) (usize 2))
                                  in
                                  let uncompressed_95 : uint_size =
                                    declassify_usize_from_uint8 (
                                      seq_index (bit_string_92) (usize 3))
                                  in
                                  let pk_78 =
                                    seq_slice (bit_string_92) (usize 4) (
                                      (pk_len_93) - (usize 2))
                                  in
                                  (pk_78)
                                end else begin (pk_78)
                                end
                              in
                              (pk_78)
                            end else begin (pk_78)
                            end
                          in
                          (pk_78)
                        end else begin (pk_78)
                        end
                      in
                      (pk_78)
                    end else begin (pk_78)
                    end
                  in
                  (pk_78)
                end else begin (pk_78)
                end
              in
              (pk_78)
            end else begin (pk_78)
            end
          in
          let seq1_77 =
            seq_slice (seq1_77) (len_81) ((seq_len (seq1_77)) - (len_81))
          in
          (seq1_77, pk_78)
        end else begin (seq1_77, pk_78)
        end
      in
      (seq1_77, pk_78))
    (seq1_77, pk_78)
  in
  if ((seq_len (pk_78)) = (usize 0)) then (Err (invalid_cert_v)) else (
    Ok (pk_78))

let concat_signature
  (r_96 : p256_scalar_t)
  (s_97 : p256_scalar_t)
  : (result signature_t crypto_error_t) =
  let signature_98 : seq uint8 =
    seq_concat_owned (
      seq_concat_owned (seq_new_ (secret (pub_u8 0x0)) (usize 0)) (
        nat_to_byte_seq_be (0xunknown) (0) (r_96))) (
      nat_to_byte_seq_be (0xunknown) (0) (s_97))
  in
  Ok (signature_98)

let p256_sign
  (ps_99 : signature_key_t)
  (payload_100 : byte_seq)
  (entropy_101 : entropy_t)
  : (result signature_t crypto_error_t) =
  let (entropy_102, _) : (seq uint8 & seq uint8) =
    seq_split_off (entropy_101) (usize 32)
  in
  let nonce_103 : p256_scalar_t =
    nat_from_byte_seq_be (0xunknown) (0) (entropy_102)
  in
  match ecdsa_p256_sha256_sign (payload_100) (
    nat_from_byte_seq_be (0xunknown) (0) (ps_99)) (nonce_103) with
  | Ok (r_104, s_105) -> concat_signature (r_104) (s_105)
  | Err _ -> Err (crypto_error_v)

let sign
  (sa_106 : signature_scheme_t)
  (ps_107 : signature_key_t)
  (payload_108 : byte_seq)
  (ent_109 : entropy_t)
  : (result signature_t crypto_error_t) =
  match sa_106 with
  | EcdsaSecp256r1Sha256_signature_scheme_t -> p256_sign (ps_107) (
    payload_108) (ent_109)
  | ED25519_signature_scheme_t -> Err (unsupported_algorithm_v)
  | RsaPssRsaSha256_signature_scheme_t -> Err (unsupported_algorithm_v)

let p256_verify
  (pk_110 : verification_key_t)
  (payload_111 : byte_seq)
  (sig_112 : byte_seq)
  : empty_result_t =
  let (pk_x_113, pk_y_114) : (p256_field_element_t & p256_field_element_t) =
    (
      nat_from_byte_seq_be (0xunknown) (0) (
        seq_slice (pk_110) (usize 0) (usize 32)),
      nat_from_byte_seq_be (0xunknown) (0) (
        seq_slice (pk_110) (usize 32) (usize 32))
    )
  in
  let (r_115, s_116) : (p256_scalar_t & p256_scalar_t) =
    (
      nat_from_byte_seq_be (0xunknown) (0) (
        seq_slice (sig_112) (usize 0) (usize 32)),
      nat_from_byte_seq_be (0xunknown) (0) (
        seq_slice (sig_112) (usize 32) (usize 32))
    )
  in
  match ecdsa_p256_sha256_verify (payload_111) ((pk_x_113, pk_y_114)) (
    (r_115, s_116)) with
  | Ok () -> Ok (())
  | Err _ -> Err (verify_failed_v)

let verify
  (sa_117 : signature_scheme_t)
  (pk_118 : verification_key_t)
  (payload_119 : byte_seq)
  (sig_120 : byte_seq)
  : empty_result_t =
  match sa_117 with
  | EcdsaSecp256r1Sha256_signature_scheme_t -> p256_verify (pk_118) (
    payload_119) (sig_120)
  | ED25519_signature_scheme_t -> Err (unsupported_algorithm_v)
  | RsaPssRsaSha256_signature_scheme_t -> Err (unsupported_algorithm_v)

let hkdf_extract
  (ha_121 : hash_algorithm_t)
  (k_122 : key_t)
  (salt_123 : key_t)
  : crypto_byte_seq_result_t =
  match ha_121 with
  | SHA256_hash_algorithm_t -> Ok (seq_from_seq (extract (salt_123) (k_122)))
  | SHA384_hash_algorithm_t -> Err (unsupported_algorithm_v)
  | SHA512_hash_algorithm_t -> Err (unsupported_algorithm_v)

let hkdf_expand
  (ha_124 : hash_algorithm_t)
  (k_125 : key_t)
  (info_126 : byte_seq)
  (len_127 : uint_size)
  : crypto_byte_seq_result_t =
  match ha_124 with
  | SHA256_hash_algorithm_t -> match expand (k_125) (info_126) (len_127) with
  | Ok b_128 -> Ok (b_128)
  | Err _ -> Err (hkdf_error_v)
  | SHA384_hash_algorithm_t -> Err (unsupported_algorithm_v)
  | SHA512_hash_algorithm_t -> Err (unsupported_algorithm_v)

let aes128_encrypt
  (k_129 : aead_key_t)
  (iv_130 : aead_iv_t)
  (payload_131 : byte_seq)
  (ad_132 : byte_seq)
  : crypto_byte_seq_result_t =
  let (ctxt_133, tag_134) : (seq uint8 & gf128_tag_t) =
    encrypt_aes128 (array_from_seq (0) (k_129)) (array_from_seq (0) (iv_130)) (
      ad_132) (payload_131)
  in
  Ok (seq_concat (ctxt_133) (tag_134))

let chacha_encrypt
  (k_135 : aead_key_t)
  (iv_136 : aead_iv_t)
  (payload_137 : byte_seq)
  (ad_138 : byte_seq)
  : crypto_byte_seq_result_t =
  let (ctxt_139, tag_140) : (seq uint8 & poly1305_tag_t) =
    chacha20_poly1305_encrypt (array_from_seq (32) (k_135)) (
      array_from_seq (12) (iv_136)) (ad_138) (payload_137)
  in
  Ok (seq_concat (ctxt_139) (tag_140))

let aead_encrypt
  (a_141 : aead_algorithm_t)
  (k_142 : aead_key_t)
  (iv_143 : aead_iv_t)
  (payload_144 : byte_seq)
  (ad_145 : byte_seq)
  : crypto_byte_seq_result_t =
  match a_141 with
  | Aes128Gcm_aead_algorithm_t -> aes128_encrypt (k_142) (iv_143) (
    payload_144) (ad_145)
  | Aes256Gcm_aead_algorithm_t -> Err (unsupported_algorithm_v)
  | Chacha20Poly1305_aead_algorithm_t -> chacha_encrypt (k_142) (iv_143) (
    payload_144) (ad_145)

let aes128_decrypt
  (k_146 : aead_key_t)
  (iv_147 : aead_iv_t)
  (ciphertext_148 : byte_seq)
  (ad_149 : byte_seq)
  : crypto_byte_seq_result_t =
  match decrypt_aes128 (array_from_seq (0) (k_146)) (
    array_from_seq (0) (iv_147)) (ad_149) (
    seq_slice_range (ciphertext_148) (
      (usize 0, (seq_len (ciphertext_148)) - (usize 16)))) (
    array_from_seq (0) (
      seq_slice_range (ciphertext_148) (
        ((seq_len (ciphertext_148)) - (usize 16), seq_len (ciphertext_148)
        )))) with
  | Ok m_150 -> Ok (m_150)
  | Err _ -> Err (mac_failed_v)

let chacha_decrypt
  (k_151 : aead_key_t)
  (iv_152 : aead_iv_t)
  (ciphertext_153 : byte_seq)
  (ad_154 : byte_seq)
  : crypto_byte_seq_result_t =
  match chacha20_poly1305_decrypt (array_from_seq (32) (k_151)) (
    array_from_seq (12) (iv_152)) (ad_154) (
    seq_slice_range (ciphertext_153) (
      (usize 0, (seq_len (ciphertext_153)) - (usize 16)))) (
    array_from_seq (16) (
      seq_slice_range (ciphertext_153) (
        ((seq_len (ciphertext_153)) - (usize 16), seq_len (ciphertext_153)
        )))) with
  | Ok ptxt_155 -> Ok (ptxt_155)
  | Err _ -> Err (mac_failed_v)

let aead_decrypt
  (a_156 : aead_algorithm_t)
  (k_157 : aead_key_t)
  (iv_158 : aead_iv_t)
  (ciphertext_159 : byte_seq)
  (ad_160 : byte_seq)
  : crypto_byte_seq_result_t =
  match a_156 with
  | Aes128Gcm_aead_algorithm_t -> aes128_decrypt (k_157) (iv_158) (
    ciphertext_159) (ad_160)
  | Aes256Gcm_aead_algorithm_t -> Err (unsupported_algorithm_v)
  | Chacha20Poly1305_aead_algorithm_t -> chacha_decrypt (k_157) (iv_158) (
    ciphertext_159) (ad_160)

