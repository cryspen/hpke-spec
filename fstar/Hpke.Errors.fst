module Hpke.Errors

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

open FStar.Mul

open Hacspec.Lib

noeq type hpke_error_t =
| ValidationError_hpke_error_t : hpke_error_t
| DeserializeError_hpke_error_t : hpke_error_t
| EncapError_hpke_error_t : hpke_error_t
| DecapError_hpke_error_t : hpke_error_t
| OpenError_hpke_error_t : hpke_error_t
| MessageLimitReachedError_hpke_error_t : hpke_error_t
| DeriveKeyPairError_hpke_error_t : hpke_error_t
| InconsistentPskInputs_hpke_error_t : hpke_error_t
| UnnecessaryPsk_hpke_error_t : hpke_error_t
| MissingPsk_hpke_error_t : hpke_error_t
| UnsupportedAlgorithm_hpke_error_t : hpke_error_t
| InvalidParameters_hpke_error_t : hpke_error_t
| CryptoError_hpke_error_t : hpke_error_t

type hpke_byte_seq_result_t = (result byte_seq hpke_error_t)

