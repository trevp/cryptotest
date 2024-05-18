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
@[simp] def enc_otp         : Bits := xor rand any
@[simp] def enc_double_otp  : Bits := xor rand (xor rand any)

theorem enc_otp_is_ind_rand         : enc_otp = rand        := by simp
theorem enc_double_otp_is_ind_rand  : enc_double_otp = rand := by simp

-- More complex proofs: CPA security
-- An encryption scheme is a pair (initial state, encryption function).
-- The encryption function maps an input state to an (output Bits, new state)
def EncryptionSchemeCPA (EncStateType: Type) : Type :=
  EncStateType × (EncStateType → (Bits × EncStateType))

-- Security definition when attacker queries one message
@[simp] def is_ind_one_time (enc_scheme: EncryptionSchemeCPA EncStateType) : Prop :=
  let (initial_state, enc_func) := enc_scheme
  let (ctxt, _state) := enc_func initial_state
  ctxt = rand

-- ...when attacker queries q messages
-- we're not tracking bounds, so this definition is only valid for small q
@[simp] def is_ind_cpa_q (enc_scheme: EncryptionSchemeCPA EncStateType) (q: Nat): Prop :=
  let (initial_state, enc_func) := enc_scheme
  let rec loop : Nat → Prop × EncStateType
    | 0   => (True, initial_state)
    | q+1 =>
        let (result, state) := loop q
        let (ctxt, new_state) := enc_func state
        (ctxt = rand ∧ result, new_state)
  (loop q).1

-- ...when attacker queries any number of messages (caveat above)
@[simp] def is_ind_cpa (enc_scheme: EncryptionSchemeCPA EncStateType): Prop :=
  ∀ (q: Nat), is_ind_cpa_q enc_scheme q

-- A simple encryption scheme: r=rand, prf(k,r) xor msg
@[simp] def enc_prf_random_init := PrfRandInputs.new rand

@[simp] def enc_prf_random_func (prf: PrfRandInputs) : Bits × PrfRandInputs :=
  let (prf_out, prf_next) := prf.prf rand_pub
  (xor any prf_out, prf_next)

@[simp] def enc_prf_random : EncryptionSchemeCPA PrfRandInputs :=
  (enc_prf_random_init, enc_prf_random_func)

-- Some lemmas used in the following proofs
@[simp] lemma enc_prf_random_doesnt_modify_state :
    ∀ (state: PrfRandInputs), (enc_prf_random_func state).2 = state := by
  intro state
  simp [enc_prf_random_func]
  split <;> rfl

@[simp] lemma enc_prf_random_loop_doesnt_modify_state :
    ∀ q,  (is_ind_cpa_q.loop enc_prf_random_init enc_prf_random_func q).2 =
          (enc_prf_random_init) := by
  intro q
  induction q with
  | zero => simp [is_ind_cpa_q.loop]
  | succ n ih => simp_all [is_ind_cpa_q.loop]

@[simp] lemma enc_prf_random_always_outputs_rand :
  (enc_prf_random_func enc_prf_random_init).1 = rand := by
  simp

theorem enc_prf_random_is_ind_one_time :
    is_ind_one_time (enc_prf_random) := by simp

theorem enc_prf_random_is_ind_cpa :
    is_ind_cpa (enc_prf_random) := by
  unfold is_ind_cpa
  intro q
  unfold is_ind_cpa_q
  split
  rename_i _ _ _ h; unfold enc_prf_random at h; cases h
  induction q with
  | zero => simp [is_ind_cpa_q.loop]
  | succ n ih =>
    unfold is_ind_cpa_q.loop
    simp only [ih]
    apply And.intro
    · rw [enc_prf_random_loop_doesnt_modify_state]
      exact enc_prf_random_always_outputs_rand
    · trivial

-- WORK IN PROGRESS:
-- Another simple encryption scheme: (n, prf(n) xor msg)
-- Adversary allowed to choose nonces n, but can't reuse them ("nonce-respecting")
-- This follows EasyCrypt's IND-NRCPA$ tutorial:
-- https://fdupress.gitlab.io/easycrypt-web/docs/simple-tutorial/security

-- The encryption function takes an additional input (Nat)
def EncryptionSchemeNRCPA (EncStateType: Type) : Type :=
  EncStateType × (Nat → EncStateType → (Bits × EncStateType))

-- We have to explicitly model the adversary now, unlike previous examples where
-- Bits.any stood in for the adversary's choices.
--
-- An adversary is a pair (initial state, adversary function).
-- The adversary function maps an input state to a nonce and new state.
-- As before, the adversary's plaintext inputs are modeled as Bits.any and the
-- game will check that ciphertexts are Bits.rand, so we don't need to explicitly
-- model the adversary's view of plaintexts and ciphertexts, only their choice of nonces.
def AdversaryNRCPA (AdvStateType: Type) : Type :=
  AdvStateType × (AdvStateType → (Nat × AdvStateType))

-- security definition when attacker queries one message
@[simp] def is_ind_nrcpa_one_time
    (enc_scheme: EncryptionSchemeNRCPA EncStateType)
    (adv: AdversaryNRCPA AdvStateType) : Prop :=
  let (initial_enc_state, enc_func) := enc_scheme
  let (initial_adv_state, adv_func) := adv
  let (n, _adv_state) := adv_func initial_adv_state
  let (ctxt, _enc_state) := enc_func n initial_enc_state
  ctxt = rand

-- ...when attacker queries q messages
-- we're not tracking bounds, so this definition is only valid for small q
@[simp] def is_ind_nrcpa_q
    (enc_scheme: EncryptionSchemeNRCPA EncStateType)
    (adv: AdversaryNRCPA AdvStateType)
    (q: Nat): Prop :=
  let (initial_enc_state, enc_func) := enc_scheme
  let (initial_adv_state, adv_func) := adv
  let rec loop : Nat → EncStateType → AdvStateType → Prop
    | 0, _enc_state, _adv_state => True
    | q+1, enc_state, adv_state =>
      let (n, new_adv_state) := adv_func adv_state
      -- TODO: Enforce nonces are non-repeating
      let (ctxt, new_enc_state) := enc_func n enc_state
      ctxt = rand ∧ loop q new_enc_state new_adv_state
  (loop q initial_enc_state initial_adv_state)

-- ...when attacker queries any number of messages (caveat above)
@[simp] def is_ind_nrcpa
    (enc_init: EncryptionSchemeNRCPA EncStateType)
    (adv_init: AdversaryNRCPA AdvStateType): Prop :=
  ∀ (q: Nat), is_ind_nrcpa_q enc_init adv_init q

-- A simple encryption scheme: (n=adv(), prf(k,n) xor msg)
def enc_prf_nr : EncryptionSchemeNRCPA PrfNumInputs :=
  (PrfNumInputs.new rand,
  fun (n: Nat) prf =>
    let (prf_out, prf_next) := prf.prf (num n)
    (xor any prf_out, prf_next))

theorem enc_prf_nr_is_ind_nrcpa_one_time
  (adv: AdversaryNRCPA AdvStateType):
    is_ind_nrcpa_one_time enc_prf_nr adv := by
  simp_all [is_ind_nrcpa_one_time, enc_prf_nr]
  split; trivial

theorem enc_prf_nr_is_ind_nrcpa
  (adv: AdversaryNRCPA AdvStateType):
    is_ind_nrcpa enc_prf_nr adv := by
  unfold is_ind_nrcpa
  intro q
  unfold is_ind_nrcpa_q
  induction q with
  | zero =>
    simp_all [is_ind_nrcpa_q.loop, enc_prf_nr]
    split; trivial
  | succ => sorry -- TODO!!!
