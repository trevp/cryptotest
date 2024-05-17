import Mathlib
open Finset

-- Fixed-length sequence of bits of cryptographic length, e.g. 128 or 256 bits
inductive Bits where
  | any           : Bits     -- any value
  | rand          : Bits     -- indistinguishable from random
  | rand_pub      : Bits     -- indistinguishable from random but public (e.g. nonce)
  | num (n: Nat)  : Bits     -- integer encoded into bits

namespace Bits

@[simp] def xor (b1: Bits) (b2: Bits) : Bits :=
  match b1, b2 with
  | rand, _ => rand
  | _, rand => rand
  | _, _ => any
end Bits

open Bits

structure PrfRandInputs where
  key : Bits

namespace PrfRandInputs

@[simp] def new (new_key: Bits) : PrfRandInputs :=
  {key := new_key }

@[simp] def prf (p: PrfRandInputs) (input: Bits) : Bits × PrfRandInputs :=
  match p.key with
  | rand =>
    match input with
    | rand | rand_pub => (rand, p)
    | _ => (any, p)
  | _ => (any, p)

end PrfRandInputs

structure PrfNumInputs where
  key : Bits
  used_nums : Finset Nat

namespace PrfNumInputs

@[simp] def new (new_key: Bits) : PrfNumInputs :=
  {key := new_key, used_nums := {} }

@[simp] def prf (p: PrfNumInputs) (input: Bits) : Bits × PrfNumInputs :=
  match p.key with
  | rand =>
    match input with
    | num n =>
      if n ∉ p.used_nums then
        (rand, {p with used_nums := p.used_nums ∪ {n} })
      else
        (any, p)
    | _ => (any, p)
  | _ => (any, p)
end PrfNumInputs

-- Simple proofs: Encryption with One-Time Pad
def enc_otp : Bits :=
  xor rand any

theorem enc_otp_is_ind_rand :
    enc_otp = rand := by
  simp [enc_otp]

def enc_double_otp : Bits :=
  xor rand (xor rand any)

theorem enc_double_otp_is_ind_rand :
    enc_double_otp = rand := by
  simp [enc_double_otp]

-- More complex proofs: CPA security

-- An encryption algorithm returns an initial state, and an encryption function
-- The encryption function maps an input state to an (output Bits, new state)
def EncryptionAlgorithmCPA (EncStateType: Type) : Type :=
  Unit → EncStateType × (EncStateType → (Bits × EncStateType))

-- security definition when attacker queries one message
@[simp] def is_ind_one_time (enc_alg: EncryptionAlgorithmCPA EncStateType) : Prop :=
  let (initial_state, enc_func) := enc_alg ()
  let (ctxt, _state) := enc_func initial_state
  ctxt = rand

-- ...when attacker queries q messages
-- we're not tracking bounds, so this proof is only valid for small q
@[simp] def is_ind_cpa_q (enc_alg: EncryptionAlgorithmCPA EncStateType) (q: Nat): Prop :=
  let (initial_state, enc_func) := enc_alg ()
  let rec loop : Nat → EncStateType → Prop
    | 0, _state   => True
    | n+1, state =>
      let (ctxt, new_state) := enc_func state
      ctxt = rand ∧ loop n new_state
  (loop q initial_state)

-- ...when attacker queries any number of messages (caveat above)
@[simp] def is_ind_cpa (enc_alg: EncryptionAlgorithmCPA EncStateType): Prop :=
  ∀ (q: Nat), is_ind_cpa_q enc_alg q

-- A simple encryption scheme: (r=rand, prf(k,r) xor msg)
def enc_prf_random : EncryptionAlgorithmCPA PrfRandInputs := fun _ =>
  (PrfRandInputs.new rand,
  fun prf =>
    let (prf_out, prf_next) := prf.prf rand_pub
    (xor any prf_out, prf_next))

theorem enc_prf_random_is_ind_one_time :
    is_ind_one_time (enc_prf_random) := by
  simp [enc_prf_random]

theorem enc_prf_random_is_ind_cpa :
    is_ind_cpa (enc_prf_random) := by
  unfold is_ind_cpa
  intro q
  unfold is_ind_cpa_q
  induction q with
  | zero => simp [is_ind_cpa_q.loop]
  | succ => simp_all [is_ind_cpa_q.loop, enc_prf_random]

-- Another simple encryption scheme: (n, prf(n) xor msg)
-- Adversary chooses nonces n, but can't reuse them (EasyCrypt example)

-- Now the encryption function takes an additional input (Nat)
def EncryptionAlgorithmNRCPA (EncStateType: Type) : Type :=
  Unit → EncStateType × (Nat → EncStateType → (Bits × EncStateType))

-- TODO
