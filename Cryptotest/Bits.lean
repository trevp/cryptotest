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
-- Adversary implicitly provides Bits.any and sees Bits.rand,
-- so we don't need to explicitly model the adversary or security game.
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

-- An encryption "init" function returns an initial state, and an encryption function
-- The encryption function maps an input state to an (output Bits, new state)
def EncryptionCPAInit (EncStateType: Type) : Type :=
  Unit → EncStateType × (EncStateType → (Bits × EncStateType))

-- security definition when attacker queries one message
@[simp] def is_ind_one_time (enc_init: EncryptionCPAInit EncStateType) : Prop :=
  let (initial_state, enc_func) := enc_init ()
  let (ctxt, _state) := enc_func initial_state
  ctxt = rand

-- ...when attacker queries q messages
-- we're not tracking bounds, so this definition is only valid for small q
@[simp] def is_ind_cpa_q (enc_init: EncryptionCPAInit EncStateType) (q: Nat): Prop :=
  let (initial_state, enc_func) := enc_init ()
  let rec loop : Nat → EncStateType → Prop
    | 0, _state   => True
    | q+1, state =>
      let (ctxt, new_state) := enc_func state
      ctxt = rand ∧ loop q new_state
  (loop q initial_state)

-- ...when attacker queries any number of messages (caveat above)
@[simp] def is_ind_cpa (enc_init: EncryptionCPAInit EncStateType): Prop :=
  ∀ (q: Nat), is_ind_cpa_q enc_init q

-- A simple encryption scheme: (r=rand, prf(k,r) xor msg)
def enc_prf_random : EncryptionCPAInit PrfRandInputs := fun _ =>
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
-- Adversary allowed to choose nonces n, but can't reuse them ("nonce-respecting")
-- This follows EasyCrypt's IND-NRCPA$ tutorial:
-- https://fdupress.gitlab.io/easycrypt-web/docs/simple-tutorial/security

-- The encryption "init" function takes an additional input (Nat)
def EncryptionNRCPAInit (EncStateType: Type) : Type :=
  Unit → EncStateType × (Nat → EncStateType → (Bits × EncStateType))

-- We have to explicitly model the adversary now, unlike previous examples where
-- Bits.any stood in for the adversary's choices.
--
-- The adversary "init" function returns an initial state and an adversary function.
-- The adversary function maps an input state to a nonce and new state.
-- As before, the adversary's plaintext inputs are modeled as Bits.any and the
-- game will check that ciphertexts are Bits.rand, so we don't need to explicitly
-- model the adversary's view of plaintexts and ciphertexts, only their choice of nonces.
def AdversaryNRCPAInit (AdvStateType: Type) : Type :=
  Unit -> AdvStateType × (AdvStateType → (Nat × AdvStateType))

-- security definition when attacker queries one message
@[simp] def is_ind_nrcpa_one_time
    (enc_init: EncryptionNRCPAInit EncStateType)
    (adv_init: AdversaryNRCPAInit AdvStateType) : Prop :=
  let (initial_enc_state, enc_func) := enc_init ()
  let (initial_adv_state, adv_func) := adv_init ()
  let (n, _adv_state) := adv_func initial_adv_state
  let (ctxt, _enc_state) := enc_func n initial_enc_state
  ctxt = rand

-- ...when attacker queries q messages
-- we're not tracking bounds, so this definition is only valid for small q
@[simp] def is_ind_nrcpa_q
    (enc_init: EncryptionNRCPAInit EncStateType)
    (adv_init: AdversaryNRCPAInit AdvStateType)
    (q: Nat): Prop :=
  let (initial_enc_state, enc_func) := enc_init ()
  let (initial_adv_state, adv_func) := adv_init ()
  let rec loop : Nat → EncStateType → AdvStateType → Prop
    | 0, _enc_state, _adv_state => True
    | q+1, enc_state, adv_state =>
      let (n, new_adv_state) := adv_func adv_state
      let (ctxt, new_enc_state) := enc_func n enc_state
      ctxt = rand ∧ loop q new_enc_state new_adv_state
  (loop q initial_enc_state initial_adv_state)

-- ...when attacker queries any number of messages (caveat above)
@[simp] def is_ind_nrcpa
    (enc_init: EncryptionNRCPAInit EncStateType)
    (adv_init: AdversaryNRCPAInit AdvStateType): Prop :=
  ∀ (q: Nat), is_ind_nrcpa_q enc_init adv_init q

-- A simple encryption scheme: (n=adv(), prf(k,n) xor msg)
def enc_prf_nr : EncryptionNRCPAInit PrfNumInputs := fun _ =>
  (PrfNumInputs.new rand,
  fun (n: Nat) prf =>
    let (prf_out, prf_next) := prf.prf (num n)
    (xor any prf_out, prf_next))

theorem enc_prf_nr_is_ind_nrcpa_one_time
  (adv_init: AdversaryNRCPAInit AdvStateType):
    is_ind_nrcpa_one_time enc_prf_nr adv_init := by
  simp [enc_prf_nr]

theorem enc_prf_nr_is_ind_nrcpa
  (adv_init: AdversaryNRCPAInit AdvStateType):
    is_ind_nrcpa enc_prf_nr adv_init := by
  unfold is_ind_nrcpa
  intro q
  unfold is_ind_nrcpa_q
  induction q with
  | zero => simp [is_ind_nrcpa_q.loop]
  | succ => sorry -- TODO!!!








-- TODO
