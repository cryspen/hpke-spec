module Hpke

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

open Hpke.Aead

open Hpke.Kdf

open Hpke.Kem

open Hpke.Errors

noeq type mode_t =
| Mode_base_mode_t : mode_t
| Mode_psk_mode_t : mode_t
| Mode_auth_mode_t : mode_t
| Mode_auth_psk_mode_t : mode_t

noeq type hpke_config_t =
| HPKEConfig_hpke_config_t : (mode_t & kem_t & kdf_t & aead_t) -> hpke_config_t

type kem_output_t = byte_seq

type ciphertext_t = byte_seq

noeq type hpke_ciphertext_t =
| HPKECiphertext_hpke_ciphertext_t : (kem_output_t & ciphertext_t
) -> hpke_ciphertext_t

type hpke_private_key_t = byte_seq

type hpke_public_key_t = byte_seq

noeq type hpke_key_pair_t =
| HPKEKeyPair_hpke_key_pair_t : (hpke_private_key_t & hpke_public_key_t
) -> hpke_key_pair_t

type additional_data_t = byte_seq

type psk_t = byte_seq

type psk_id_t = byte_seq

let info_hash_label () : byte_seq =
  array_from_list (
    let l =
      [
        secret (pub_u8 0x69);
        secret (pub_u8 0x6e);
        secret (pub_u8 0x66);
        secret (pub_u8 0x6f);
        secret (pub_u8 0x5f);
        secret (pub_u8 0x68);
        secret (pub_u8 0x61);
        secret (pub_u8 0x73);
        secret (pub_u8 0x68)
      ]
    in assert_norm (List.Tot.length l == 9); l)

let psk_id_hash_label () : byte_seq =
  array_from_list (
    let l =
      [
        secret (pub_u8 0x70);
        secret (pub_u8 0x73);
        secret (pub_u8 0x6b);
        secret (pub_u8 0x5f);
        secret (pub_u8 0x69);
        secret (pub_u8 0x64);
        secret (pub_u8 0x5f);
        secret (pub_u8 0x68);
        secret (pub_u8 0x61);
        secret (pub_u8 0x73);
        secret (pub_u8 0x68)
      ]
    in assert_norm (List.Tot.length l == 11); l)

let secret_label () : byte_seq =
  array_from_list (
    let l =
      [
        secret (pub_u8 0x73);
        secret (pub_u8 0x65);
        secret (pub_u8 0x63);
        secret (pub_u8 0x72);
        secret (pub_u8 0x65);
        secret (pub_u8 0x74)
      ]
    in assert_norm (List.Tot.length l == 6); l)

let key_label () : byte_seq =
  array_from_list (
    let l =
      [secret (pub_u8 0x6b); secret (pub_u8 0x65); secret (pub_u8 0x79)]
    in assert_norm (List.Tot.length l == 3); l)

let base_nonce_label () : byte_seq =
  array_from_list (
    let l =
      [
        secret (pub_u8 0x62);
        secret (pub_u8 0x61);
        secret (pub_u8 0x73);
        secret (pub_u8 0x65);
        secret (pub_u8 0x5f);
        secret (pub_u8 0x6e);
        secret (pub_u8 0x6f);
        secret (pub_u8 0x6e);
        secret (pub_u8 0x63);
        secret (pub_u8 0x65)
      ]
    in assert_norm (List.Tot.length l == 10); l)

let exp_label () : byte_seq =
  array_from_list (
    let l =
      [secret (pub_u8 0x65); secret (pub_u8 0x78); secret (pub_u8 0x70)]
    in assert_norm (List.Tot.length l == 3); l)

let sec_label () : byte_seq =
  array_from_list (
    let l =
      [secret (pub_u8 0x73); secret (pub_u8 0x65); secret (pub_u8 0x63)]
    in assert_norm (List.Tot.length l == 3); l)

let hpke_mode_label (mode_0 : mode_t) : byte_seq =
  match mode_0 with
  | Mode_base_mode_t -> array_from_list (
    let l =
      [secret (pub_u8 0x0)]
    in assert_norm (List.Tot.length l == 1); l)
  | Mode_psk_mode_t -> array_from_list (
    let l =
      [secret (pub_u8 0x1)]
    in assert_norm (List.Tot.length l == 1); l)
  | Mode_auth_mode_t -> array_from_list (
    let l =
      [secret (pub_u8 0x2)]
    in assert_norm (List.Tot.length l == 1); l)
  | Mode_auth_psk_mode_t -> array_from_list (
    let l =
      [secret (pub_u8 0x3)]
    in assert_norm (List.Tot.length l == 1); l)

let hpke_aead_value (aead_id_1 : aead_t) : uint16 =
  match aead_id_1 with
  | AES_128_GCM_aead_t -> secret (pub_u16 0x1)
  | AES_256_GCM_aead_t -> secret (pub_u16 0x2)
  | ChaCha20Poly1305_aead_t -> secret (pub_u16 0x3)
  | Export_only_aead_t -> secret (pub_u16 0xffff)

let kem (config_2 : hpke_config_t) : kem_t =
  let HPKEConfig_hpke_config_t ((_, kem_3, _, _)) : hpke_config_t =
    config_2
  in
  kem_3

type encoded_hpke_public_key_t = byte_seq

type exporter_secret_t = byte_seq

type sequence_counter_t = pub_uint32

type context_t = (key_t & nonce_t & sequence_counter_t & exporter_secret_t)

type sender_context_t = (encoded_hpke_public_key_t & context_t)

type sender_context_result_t = (result sender_context_t hpke_error_t)

type context_result_t = (result context_t hpke_error_t)

type empty_result_t = (result () hpke_error_t)

let suite_id (config_4 : hpke_config_t) : byte_seq =
  let HPKEConfig_hpke_config_t ((_, kem_5, kdf_6, aead_7)) : hpke_config_t =
    config_4
  in
  seq_concat (
    seq_concat (
      seq_concat (
        array_from_list (
          let l =
            [
              secret (pub_u8 0x48);
              secret (pub_u8 0x50);
              secret (pub_u8 0x4b);
              secret (pub_u8 0x45)
            ]
          in assert_norm (List.Tot.length l == 4); l)) (
        uint16_to_be_bytes (kem_value (kem_5)))) (
      uint16_to_be_bytes (kdf_value (kdf_6)))) (
    uint16_to_be_bytes (hpke_aead_value (aead_7)))

let default_psk () : byte_seq =
  seq_new_ (secret (pub_u8 0x0)) (usize 0)

let default_psk_id () : byte_seq =
  seq_new_ (secret (pub_u8 0x0)) (usize 0)

let empty_bytes () : byte_seq =
  seq_new_ (secret (pub_u8 0x0)) (usize 0)

let verify_psk_inputs
  (config_8 : hpke_config_t)
  (psk_9 : psk_t)
  (psk_id_10 : psk_id_t)
  : empty_result_t =
  let HPKEConfig_hpke_config_t (
      (mode_11, kem_12, kdf_13, aead_14)) : hpke_config_t =
    config_8
  in
  let got_psk_15 : bool =
    (seq_len (psk_9)) <> (usize 0)
  in
  let got_psk_id_16 : bool =
    (seq_len (psk_id_10)) <> (usize 0)
  in
  if ((got_psk_15) <> (got_psk_id_16)) then (
    Err (InconsistentPskInputs_hpke_error_t)) else (
    if (
      (got_psk_15) && (
        ((mode_11) = (Mode_base_mode_t)) || (
          (mode_11) = (Mode_auth_mode_t)))) then (
      Err (UnnecessaryPsk_hpke_error_t)) else (
      if (
        (not (got_psk_15)) && (
          ((mode_11) = (Mode_psk_mode_t)) || (
            (mode_11) = (Mode_auth_psk_mode_t)))) then (
        Err (MissingPsk_hpke_error_t)) else (Ok (()))))

let key_schedule
  (config_17 : hpke_config_t)
  (shared_secret_18 : shared_secret_t)
  (info_19 : info_t)
  (psk_20 : psk_t)
  (psk_id_21 : psk_id_t)
  : context_result_t =
  match (verify_psk_inputs (config_17) (psk_20) (psk_id_21)) with
  | Err x -> Err x
  | Ok  _  ->
    let HPKEConfig_hpke_config_t (
        (mode_22, kem_23, kdf_24, aead_25)) : hpke_config_t =
      config_17
    in
    match (
      labeled_extract (kdf_24) (suite_id (config_17)) (empty_bytes ()) (
        psk_id_hash_label ()) (psk_id_21)) with
    | Err x -> Err x
    | Ok  psk_id_hash_26 : seq uint8 ->
      match (
        labeled_extract (kdf_24) (suite_id (config_17)) (empty_bytes ()) (
          info_hash_label ()) (info_19)) with
      | Err x -> Err x
      | Ok  info_hash_27 : seq uint8 ->
        let key_schedule_context_28 : seq uint8 =
          seq_concat_owned (
            seq_concat_owned (hpke_mode_label (mode_22)) (psk_id_hash_26)) (
            info_hash_27)
        in
        match (
          labeled_extract (kdf_24) (suite_id (config_17)) (shared_secret_18) (
            secret_label ()) (psk_20)) with
        | Err x -> Err x
        | Ok  secret_29 : seq uint8 ->
          match (
            labeled_expand (kdf_24) (suite_id (config_17)) (secret_29) (
              key_label ()) (key_schedule_context_28) (nk (aead_25))) with
          | Err x -> Err x
          | Ok  key_30 : seq uint8 ->
            match (
              labeled_expand (kdf_24) (suite_id (config_17)) (secret_29) (
                base_nonce_label ()) (key_schedule_context_28) (
                nn (aead_25))) with
            | Err x -> Err x
            | Ok  base_nonce_31 : seq uint8 ->
              match (
                labeled_expand (kdf_24) (suite_id (config_17)) (secret_29) (
                  exp_label ()) (key_schedule_context_28) (nh (kdf_24))) with
              | Err x -> Err x
              | Ok  exporter_secret_32 : seq uint8 ->
                Ok ((key_30, base_nonce_31, pub_u32 0x0, exporter_secret_32))

let setup_base_s
  (config_33 : hpke_config_t)
  (pk_r_34 : hpke_public_key_t)
  (info_35 : info_t)
  (randomness_36 : randomness_t)
  : sender_context_result_t =
  match (encap (kem (config_33)) (pk_r_34) (randomness_36)) with
  | Err x -> Err x
  | Ok  (shared_secret_37, enc_38) : (seq uint8 & seq uint8) ->
    match (
      key_schedule (config_33) (shared_secret_37) (info_35) (default_psk ()) (
        default_psk_id ())) with
    | Err x -> Err x
    | Ok  key_schedule_39 : context_t ->
      Ok ((enc_38, key_schedule_39))

let setup_base_r
  (config_40 : hpke_config_t)
  (enc_41 : encoded_hpke_public_key_t)
  (sk_r_42 : hpke_private_key_t)
  (info_43 : info_t)
  : context_result_t =
  match (decap (kem (config_40)) (enc_41) (sk_r_42)) with
  | Err x -> Err x
  | Ok  shared_secret_44 : seq uint8 ->
    match (
      key_schedule (config_40) (shared_secret_44) (info_43) (default_psk ()) (
        default_psk_id ())) with
    | Err x -> Err x
    | Ok  key_schedule_45 : context_t ->
      Ok (key_schedule_45)

let setup_psks
  (config_46 : hpke_config_t)
  (pk_r_47 : hpke_public_key_t)
  (info_48 : info_t)
  (psk_49 : psk_t)
  (psk_id_50 : psk_id_t)
  (randomness_51 : randomness_t)
  : sender_context_result_t =
  match (encap (kem (config_46)) (pk_r_47) (randomness_51)) with
  | Err x -> Err x
  | Ok  (shared_secret_52, enc_53) : (seq uint8 & seq uint8) ->
    match (
      key_schedule (config_46) (shared_secret_52) (info_48) (psk_49) (
        psk_id_50)) with
    | Err x -> Err x
    | Ok  key_schedule_54 : context_t ->
      Ok ((enc_53, key_schedule_54))

let setup_pskr
  (config_55 : hpke_config_t)
  (enc_56 : encoded_hpke_public_key_t)
  (sk_r_57 : hpke_private_key_t)
  (info_58 : info_t)
  (psk_59 : psk_t)
  (psk_id_60 : psk_id_t)
  : context_result_t =
  match (decap (kem (config_55)) (enc_56) (sk_r_57)) with
  | Err x -> Err x
  | Ok  shared_secret_61 : seq uint8 ->
    match (
      key_schedule (config_55) (shared_secret_61) (info_58) (psk_59) (
        psk_id_60)) with
    | Err x -> Err x
    | Ok  key_schedule_62 : context_t ->
      Ok (key_schedule_62)

let setup_auth_s
  (config_63 : hpke_config_t)
  (pk_r_64 : hpke_public_key_t)
  (info_65 : info_t)
  (sk_s_66 : private_key_t)
  (randomness_67 : randomness_t)
  : sender_context_result_t =
  match (auth_encap (kem (config_63)) (pk_r_64) (sk_s_66) (randomness_67)) with
  | Err x -> Err x
  | Ok  (shared_secret_68, enc_69) : (seq uint8 & seq uint8) ->
    match (
      key_schedule (config_63) (shared_secret_68) (info_65) (default_psk ()) (
        default_psk_id ())) with
    | Err x -> Err x
    | Ok  key_schedule_70 : context_t ->
      Ok ((enc_69, key_schedule_70))

let setup_auth_r
  (config_71 : hpke_config_t)
  (enc_72 : encoded_hpke_public_key_t)
  (sk_r_73 : hpke_private_key_t)
  (info_74 : info_t)
  (pk_s_75 : public_key_t)
  : context_result_t =
  match (auth_decap (kem (config_71)) (enc_72) (sk_r_73) (pk_s_75)) with
  | Err x -> Err x
  | Ok  shared_secret_76 : seq uint8 ->
    match (
      key_schedule (config_71) (shared_secret_76) (info_74) (default_psk ()) (
        default_psk_id ())) with
    | Err x -> Err x
    | Ok  key_schedule_77 : context_t ->
      Ok (key_schedule_77)

let setup_auth_psks
  (config_78 : hpke_config_t)
  (pk_r_79 : hpke_public_key_t)
  (info_80 : info_t)
  (psk_81 : psk_t)
  (psk_id_82 : psk_id_t)
  (sk_s_83 : hpke_private_key_t)
  (randomness_84 : randomness_t)
  : sender_context_result_t =
  match (auth_encap (kem (config_78)) (pk_r_79) (sk_s_83) (randomness_84)) with
  | Err x -> Err x
  | Ok  (shared_secret_85, enc_86) : (seq uint8 & seq uint8) ->
    match (
      key_schedule (config_78) (shared_secret_85) (info_80) (psk_81) (
        psk_id_82)) with
    | Err x -> Err x
    | Ok  key_schedule_87 : context_t ->
      Ok ((enc_86, key_schedule_87))

let setup_auth_pskr
  (config_88 : hpke_config_t)
  (enc_89 : encoded_hpke_public_key_t)
  (sk_r_90 : hpke_private_key_t)
  (info_91 : info_t)
  (psk_92 : psk_t)
  (psk_id_93 : psk_id_t)
  (pk_s_94 : public_key_t)
  : context_result_t =
  match (auth_decap (kem (config_88)) (enc_89) (sk_r_90) (pk_s_94)) with
  | Err x -> Err x
  | Ok  shared_secret_95 : seq uint8 ->
    match (
      key_schedule (config_88) (shared_secret_95) (info_91) (psk_92) (
        psk_id_93)) with
    | Err x -> Err x
    | Ok  key_schedule_96 : context_t ->
      Ok (key_schedule_96)

let compute_nonce
  (aead_id_97 : aead_t)
  (base_nonce_98 : nonce_t)
  (seq_99 : sequence_counter_t)
  : byte_seq =
  let seq_100 : uint32_word_t =
    uint32_to_be_bytes (secret (seq_99))
  in
  let nn_101 : uint_size =
    nn (aead_id_97)
  in
  let seq_bytes_102 : seq uint8 =
    seq_new_ (secret (pub_u8 0x0)) (nn_101)
  in
  let seq_bytes_102 =
    seq_update_slice (seq_bytes_102) ((nn_101) - (usize 4)) (seq_100) (
      usize 0) (usize 4)
  in
  (seq_clone (base_nonce_98)) `seq_xor (^.)` (seq_bytes_102)

let context_s_seal
  (aead_id_103 : aead_t)
  (context_104 : context_t)
  (aad_105 : byte_seq)
  (pt_106 : byte_seq)
  : (result (ciphertext_t & context_t) hpke_error_t) =
  let (key_107, base_nonce_108, seq_109, exp_110) : (
      key_t &
      nonce_t &
      sequence_counter_t &
      exporter_secret_t
    ) =
    context_104
  in
  let nonce_111 : seq uint8 =
    compute_nonce (aead_id_103) (base_nonce_108) (seq_109)
  in
  match (aead_seal (aead_id_103) (key_107) (nonce_111) (aad_105) (pt_106)) with
  | Err x -> Err x
  | Ok  ct_112 : seq uint8 ->
    match (increment_seq (aead_id_103) (seq_109)) with
    | Err x -> Err x
    | Ok  seq_113 : sequence_counter_t ->
      Ok ((ct_112, (key_107, base_nonce_108, seq_113, exp_110)))

let context_r_open
  (aead_id_114 : aead_t)
  (context_115 : context_t)
  (aad_116 : byte_seq)
  (ct_117 : byte_seq)
  : (result (byte_seq & context_t) hpke_error_t) =
  let (key_118, base_nonce_119, seq_120, exp_121) : (
      key_t &
      nonce_t &
      sequence_counter_t &
      exporter_secret_t
    ) =
    context_115
  in
  let nonce_122 : seq uint8 =
    compute_nonce (aead_id_114) (base_nonce_119) (seq_120)
  in
  match (aead_open (aead_id_114) (key_118) (nonce_122) (aad_116) (ct_117)) with
  | Err x -> Err x
  | Ok  pt_123 : seq uint8 ->
    match (increment_seq (aead_id_114) (seq_120)) with
    | Err x -> Err x
    | Ok  seq_124 : sequence_counter_t ->
      Ok ((pt_123, (key_118, base_nonce_119, seq_124, exp_121)))

let increment_seq
  (aead_id_125 : aead_t)
  (seq_126 : sequence_counter_t)
  : (result sequence_counter_t hpke_error_t) =
  if (
    (cast U128 PUB (seq_126)) >=. (
      ((pub_u128 0x1) `shift_left` ((usize 8) * (nn (aead_id_125)))) -. (
        pub_u128 0x1))) then (
    Err (MessageLimitReachedError_hpke_error_t)) else (
    Ok ((seq_126) +. (pub_u32 0x1)))

let context_export
  (config_127 : hpke_config_t)
  (context_128 : context_t)
  (exporter_context_129 : byte_seq)
  (l_130 : uint_size)
  : hpke_byte_seq_result_t =
  let (_, _, _, exporter_secret_131) : (
      key_t &
      nonce_t &
      sequence_counter_t &
      exporter_secret_t
    ) =
    context_128
  in
  let HPKEConfig_hpke_config_t ((_, _, kdf_id_132, _)) : hpke_config_t =
    config_127
  in
  labeled_expand (kdf_id_132) (suite_id (config_127)) (exporter_secret_131) (
    sec_label ()) (exporter_context_129) (l_130)

let hpke_seal
  (config_133 : hpke_config_t)
  (pk_r_134 : hpke_public_key_t)
  (info_135 : info_t)
  (aad_136 : additional_data_t)
  (ptxt_137 : byte_seq)
  (psk_138 : (option psk_t))
  (psk_id_139 : (option psk_id_t))
  (sk_s_140 : (option hpke_private_key_t))
  (randomness_141 : randomness_t)
  : (result hpke_ciphertext_t hpke_error_t) =
  let HPKEConfig_hpke_config_t (
      (mode_142, kem_143, kdf_144, aead_145)) : hpke_config_t =
    config_133
  in
  match (
    match mode_142 with
    | Mode_base_mode_t -> setup_base_s (config_133) (pk_r_134) (info_135) (
      randomness_141)
    | Mode_psk_mode_t -> setup_psks (config_133) (pk_r_134) (info_135) (
      option_unwrap (psk_138)) (option_unwrap (psk_id_139)) (randomness_141)
    | Mode_auth_mode_t -> setup_auth_s (config_133) (pk_r_134) (info_135) (
      option_unwrap (sk_s_140)) (randomness_141)
    | Mode_auth_psk_mode_t -> setup_auth_psks (config_133) (pk_r_134) (
      info_135) (option_unwrap (psk_138)) (option_unwrap (psk_id_139)) (
      option_unwrap (sk_s_140)) (randomness_141)) with
  | Err x -> Err x
  | Ok  (enc_146, (key_147, nonce_148, _, _)) : sender_context_t ->
    match (aead_seal (aead_145) (key_147) (nonce_148) (aad_136) (ptxt_137)) with
    | Err x -> Err x
    | Ok  ct_149 : seq uint8 ->
      Ok (HPKECiphertext_hpke_ciphertext_t ((enc_146, ct_149)))

let hpke_open
  (config_150 : hpke_config_t)
  (ctxt_151 : hpke_ciphertext_t)
  (sk_r_152 : hpke_private_key_t)
  (info_153 : info_t)
  (aad_154 : additional_data_t)
  (psk_155 : (option psk_t))
  (psk_id_156 : (option psk_id_t))
  (pk_s_157 : (option hpke_public_key_t))
  : hpke_byte_seq_result_t =
  let HPKEConfig_hpke_config_t (
      (mode_158, kem_159, kdf_160, aead_161)) : hpke_config_t =
    config_150
  in
  let HPKECiphertext_hpke_ciphertext_t ((enc_162, ct_163)) : hpke_ciphertext_t =
    ctxt_151
  in
  match (
    match mode_158 with
    | Mode_base_mode_t -> setup_base_r (config_150) (enc_162) (sk_r_152) (
      info_153)
    | Mode_psk_mode_t -> setup_pskr (config_150) (enc_162) (sk_r_152) (
      info_153) (option_unwrap (psk_155)) (option_unwrap (psk_id_156))
    | Mode_auth_mode_t -> setup_auth_r (config_150) (enc_162) (sk_r_152) (
      info_153) (option_unwrap (pk_s_157))
    | Mode_auth_psk_mode_t -> setup_auth_pskr (config_150) (enc_162) (
      sk_r_152) (info_153) (option_unwrap (psk_155)) (
      option_unwrap (psk_id_156)) (option_unwrap (pk_s_157))) with
  | Err x -> Err x
  | Ok  (key_164, nonce_165, _, _) : context_t ->
    match (aead_open (aead_161) (key_164) (nonce_165) (aad_154) (ct_163)) with
    | Err x -> Err x
    | Ok  ptxt_166 : seq uint8 ->
      Ok (ptxt_166)

let send_export
  (config_167 : hpke_config_t)
  (pk_r_168 : hpke_public_key_t)
  (info_169 : info_t)
  (exporter_context_170 : byte_seq)
  (l_171 : uint_size)
  (psk_172 : (option psk_t))
  (psk_id_173 : (option psk_id_t))
  (sk_s_174 : (option hpke_private_key_t))
  (randomness_175 : randomness_t)
  : (result hpke_ciphertext_t hpke_error_t) =
  let HPKEConfig_hpke_config_t (
      (mode_176, kem_177, kdf_178, aead_179)) : hpke_config_t =
    config_167
  in
  match (
    match mode_176 with
    | Mode_base_mode_t -> setup_base_s (config_167) (pk_r_168) (info_169) (
      randomness_175)
    | Mode_psk_mode_t -> setup_psks (config_167) (pk_r_168) (info_169) (
      option_unwrap (psk_172)) (option_unwrap (psk_id_173)) (randomness_175)
    | Mode_auth_mode_t -> setup_auth_s (config_167) (pk_r_168) (info_169) (
      option_unwrap (sk_s_174)) (randomness_175)
    | Mode_auth_psk_mode_t -> setup_auth_psks (config_167) (pk_r_168) (
      info_169) (option_unwrap (psk_172)) (option_unwrap (psk_id_173)) (
      option_unwrap (sk_s_174)) (randomness_175)) with
  | Err x -> Err x
  | Ok  (enc_180, ctx_181) : sender_context_t ->
    match (
      context_export (config_167) (ctx_181) (exporter_context_170) (l_171)) with
    | Err x -> Err x
    | Ok  exported_182 : seq uint8 ->
      Ok (HPKECiphertext_hpke_ciphertext_t ((enc_180, exported_182)))

let receive_export
  (config_183 : hpke_config_t)
  (ctxt_184 : hpke_ciphertext_t)
  (sk_r_185 : hpke_private_key_t)
  (info_186 : info_t)
  (exporter_context_187 : byte_seq)
  (l_188 : uint_size)
  (psk_189 : (option psk_t))
  (psk_id_190 : (option psk_id_t))
  (pk_s_191 : (option hpke_public_key_t))
  : hpke_byte_seq_result_t =
  let HPKEConfig_hpke_config_t (
      (mode_192, kem_193, kdf_194, aead_195)) : hpke_config_t =
    config_183
  in
  let HPKECiphertext_hpke_ciphertext_t ((enc_196, ct_197)) : hpke_ciphertext_t =
    ctxt_184
  in
  match (
    match mode_192 with
    | Mode_base_mode_t -> setup_base_r (config_183) (enc_196) (sk_r_185) (
      info_186)
    | Mode_psk_mode_t -> setup_pskr (config_183) (enc_196) (sk_r_185) (
      info_186) (option_unwrap (psk_189)) (option_unwrap (psk_id_190))
    | Mode_auth_mode_t -> setup_auth_r (config_183) (enc_196) (sk_r_185) (
      info_186) (option_unwrap (pk_s_191))
    | Mode_auth_psk_mode_t -> setup_auth_pskr (config_183) (enc_196) (
      sk_r_185) (info_186) (option_unwrap (psk_189)) (
      option_unwrap (psk_id_190)) (option_unwrap (pk_s_191))) with
  | Err x -> Err x
  | Ok  ctx_198 : context_t ->
    context_export (config_183) (ctx_198) (exporter_context_187) (l_188)

