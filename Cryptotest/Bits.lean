import Mathlib
open Finset

/-
Bits is a fixed-length sequence of bits of cryptographic length, e.g. 128 or 256 bits.

Every occurrence of Bits.rand or Bits.rand_pub in an expression represents a fresh
random value.  To reuse a random value it must be "captured" in some other object,
e.g. a Prf.

Bits.any could be anything, so is used for adversary-chosen plaintexts, or the output
of calculations when we can't reason about them more precisely.  Bits.rand or rand_pub
take priority over Bits.any in expressions, so "xor rand any = rand", because "any" has
a fixed value before "rand" makes a random choice, so "any" and "rand" won't collide.
-/
inductive Bits where
  | any           : Bits     -- any value
  | rand          : Bits     -- indistinguishable from random
  | rand_pub      : Bits     -- indistinguishable from random but public (e.g. nonce)
  | num (n: Nat)  : Bits     -- integer encoded into bits

namespace Bits

@[simp] def xor (b1: Bits) (b2: Bits) : Bits :=
  match b1, b2 with
  | rand, _ => rand -- XOR of fresh random with anything is random
  | _, rand => rand -- " "
  | _, _ => any     -- Otherwise we can't reason about the output, so return "any"
end Bits

open Bits

-- If constructed with a key that is Bits.rand, the PRF object "captures" a
-- particular value for the key and reuses it.
structure PrfRandInputs where
  key : Bits

namespace PrfRandInputs

@[simp] def new (new_key: Bits) : PrfRandInputs :=
  {key := new_key }

@[simp] def prf (p: PrfRandInputs) (input: Bits) : Bits × PrfRandInputs :=
  match p.key with
  | rand =>
    match input with
    | rand | rand_pub => (rand, p) -- PRF with rand key and nonrepeating output = rand
    | _ => (any, p)
  | _ => (any, p)

end PrfRandInputs

structure PrfNumInputs where
  key : Bits -- If key is Bits.rand then the PRF "captures" the key and reuses it
  used_nums : Finset Nat -- Records all inputs to detect reuse

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

/- Simple proofs: Encryption with One-Time Pad
Adversary implicitly provides Bits.any and sees Bits.rand, so we don't
need to model the adversary or security game. Proofs are handled
automatically by Lean's simplifier tactic. Try replacing simp with
simp? to see the definitions used in proof. -/
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
    | 0      => (True, initial_state)
    | nq + 1 =>
        let (result, state) := loop nq
        let (ctxt, new_state) := enc_func state
        (result ∧ ctxt = rand, new_state)
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

-- Proof of one-time security
theorem enc_prf_random_is_ind_one_time :
  is_ind_one_time enc_prf_random := by simp

-- Some lemmas used in the following proof of IND-CPA security
lemma enc_prf_random_loop_outputs_init_state :
    ∀ q,  (is_ind_cpa_q.loop enc_prf_random_init enc_prf_random_func q).2 =
          (enc_prf_random_init) := by
  intro q
  induction q with
  | zero => simp [is_ind_cpa_q.loop]
  | succ => simp_all [is_ind_cpa_q.loop]

lemma enc_prf_random_with_init_state_outputs_rand :
  (enc_prf_random_func enc_prf_random_init).1 = rand := by simp

-- Main proof of this section.  A simple proof by induction.
-- IF is_ind_cpa for n queries (induction hypothesis ih),
-- THEN is_ind_cpa for n+1 queries because of the lemmas
theorem enc_prf_random_is_ind_cpa :
    is_ind_cpa (enc_prf_random) := by
  unfold is_ind_cpa
  intro q
  unfold is_ind_cpa_q
  split
  rename_i _ _ _ h; unfold enc_prf_random at h; cases h
  induction q with
  | zero =>
    unfold is_ind_cpa_q.loop; simp
  | succ _ ih =>
    unfold is_ind_cpa_q.loop
    simp only [ih]
    apply And.intro; trivial
    rw [enc_prf_random_loop_outputs_init_state]
    exact enc_prf_random_with_init_state_outputs_rand

-- WORK IN PROGRESS:
/-Another simple encryption scheme: (n, prf(n) xor msg)
  Adversary allowed to choose nonces n, but can't reuse them ("nonce-respecting").
  This follows EasyCrypt's IND-NRCPA$ tutorial:
  https://fdupress.gitlab.io/easycrypt-web/docs/simple-tutorial/security
-/

-- The encryption function takes an additional input (Nat)
def EncryptionSchemeNRCPA (EncStateType: Type) : Type :=
  EncStateType × (Nat → EncStateType → (Bits × EncStateType))

/-
We have to explicitly model the adversary now, unlike previous examples where
Bits.any stood in for all adversary choices.

An adversary is a pair (initial state, adversary function). The adversary
function maps an input state to a nonce and new state. As before, the
adversary's plaintext inputs are modeled as Bits.any and the game will check
that ciphertexts are Bits.rand, so we don't need to explicitly model the
adversary's view of plaintexts and ciphertexts, only their choice of nonces.
-/
def AdversaryNRCPA (AdvStateType: Type) : Type :=
  AdvStateType × (AdvStateType → (Nat × AdvStateType))

-- Security definition when attacker queries one message
@[simp] def is_ind_nrcpa_one_time
    (enc_scheme: EncryptionSchemeNRCPA EncStateType)
    (adv: AdversaryNRCPA AdvStateType) : Prop :=
  let (initial_enc_state, enc_func) := enc_scheme
  let (initial_adv_state, adv_func) := adv
  let (n, _adv_state) := adv_func initial_adv_state
  let (ctxt, _enc_state) := enc_func n initial_enc_state
  ctxt = rand

-- Security definition when attacker queries q messages
@[simp] def is_ind_nrcpa_q
    (enc_scheme: EncryptionSchemeNRCPA EncStateType)
    (adv: AdversaryNRCPA AdvStateType)
    (q: Nat): Prop :=
  let (initial_enc_state, enc_func) := enc_scheme
  let (initial_adv_state, adv_func) := adv
  let rec loop : Nat → Prop × EncStateType × AdvStateType × Finset Nat × Bool
    | 0       =>    (True, initial_enc_state, initial_adv_state, {}, false)
    | nq + 1  =>
      let (result, enc_state, adv_state, used_nums, bad_adv) := loop nq
      if bad_adv then
        (True, enc_state, adv_state, used_nums, bad_adv)
      else
        let (n, new_adv_state) := adv_func adv_state
        if n ∈ used_nums then  -- bad adversary reuses nonce, thus loses game
          (True, enc_state, adv_state, used_nums, true)
        else
          let new_used_nums := used_nums ∪ {n}
          let (ctxt, new_enc_state) := enc_func n enc_state
          (result ∧ ctxt = rand, new_enc_state, new_adv_state, new_used_nums, false)
  (loop q).1

-- ...when attacker queries any number of messages
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
  simp [is_ind_nrcpa_one_time, enc_prf_nr]
  split; trivial

theorem enc_prf_nr_is_ind_nrcpa
  (adv: AdversaryNRCPA AdvStateType):
    is_ind_nrcpa enc_prf_nr adv := by
  unfold is_ind_nrcpa
  intro q
  unfold is_ind_nrcpa_q
  split
  rename_i _ _ _ h
  unfold enc_prf_nr at h
  cases h
  induction q with
  | zero =>
    unfold is_ind_nrcpa_q.loop
    split; simp
  | succ _ ih => sorry -- TODO
