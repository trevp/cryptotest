import Mathlib
open Finset

-- Bits is a fixed-length sequence of bits of cryptographic length, e.g. 128 or 256 bits.
inductive Bits where
  | any           : Bits     -- any value
  | rand          : Bits     -- indistinguishable from random
  | rand_pub      : Bits     -- indistinguishable from random but public (e.g. nonce)
  | num (n: Nat)  : Bits     -- integer encoded into bits

namespace Bits
@[simp] def xor (b1: Bits) (b2: Bits) : Bits :=
  match b1, b2 with
  | rand, _ => rand -- XOR of random with anything is random
  | _, rand => rand
  | _, _    => any  -- Otherwise "any"
end Bits
open Bits

-- This PRF will always return rand if evaluated on rand or rand_pub inputs.
structure PrfRandInputs

namespace PrfRandInputs

@[simp] def new : Bits → PrfRandInputs × Bool
  | rand => ({}, true)
  | _ => ({}, false)

@[simp] def eval (prf: PrfRandInputs) : Bits →  Bits × PrfRandInputs
  | rand | rand_pub => (rand, prf)
  | _ => (any, prf)

end PrfRandInputs

-- This PRF will always return rand if evaluated on nonrepeating numbered inputs.
structure PrfNumInputs where
  used_nums : Finset Nat

namespace PrfNumInputs

@[simp] def new : Bits → PrfNumInputs × Bool
  | rand => ({used_nums := {}}, true)
  | _ => ({used_nums := {}}, false)

@[simp] def eval (prf: PrfNumInputs) : Bits → Bits × PrfNumInputs
  | num n =>
    if n ∉ prf.used_nums then (rand, {prf with used_nums := prf.used_nums ∪ {n} })
    else (any, prf)
  | _ => (any, prf)

end PrfNumInputs

-- Simple proofs: Encryption with One-Time Pad
----------------------------------------------
@[simp] def enc_otp         : Bits := xor rand any
@[simp] def enc_double_otp  : Bits := xor rand (xor rand any)

theorem is_ind_enc_otp        : enc_otp = rand        := by simp
theorem is_ind_enc_double_otp : enc_double_otp = rand := by simp

-- CPA security of simple PRF encryption scheme
-----------------------------------------------
structure EncryptionScheme (EncStateType: Type) where
  initial_state : EncStateType
  enc_func : EncStateType → (Bits × EncStateType)

-- Security definition
@[simp] def is_cpa (scheme: EncryptionScheme EncStateType) : Prop :=
  ∃ (sec_invariant: EncStateType → Prop),
      (sec_invariant scheme.initial_state) ∧
      ∀ (s: EncStateType),
        sec_invariant s →
          (scheme.enc_func s).1 = rand ∧
          sec_invariant (scheme.enc_func s).2

-- The simple encryption scheme: r=rand, prf(k,r) xor msg
@[simp] def enc_prf_random : EncryptionScheme PrfRandInputs :=
  {initial_state := (PrfRandInputs.new rand).1,
   enc_func := fun prf => let (prf_out, prf_next) := prf.eval rand_pub
                          (xor prf_out any, prf_next)}

-- Security proof
theorem is_cpa_enc_prf_random: is_cpa enc_prf_random := by
  use fun _ => True  -- security invariant (True for all inputs)
  simp

-- CPA security of nonce-based PRF encryption scheme
-- Adversary allowed to choose nonces n, but can't reuse them.
-- Similar to Easycrypt example:
--   https://fdupress.gitlab.io/easycrypt-web/
--   https://gitlab.com/fdupress/easycrypt-tutorial
--------------------------------------------------------------
structure EncryptionSchemeWithNonce (EncStateType: Type) where
  initial_state : EncStateType
  enc_func : EncStateType → Nat → (Bits × EncStateType)

variable (scheme: EncryptionSchemeWithNonce EncStateType)

-- The adversary interacts with a stateful game:
structure NRGameState (EncStateType: Type) where
  enc_state : EncStateType
  used_nums : Finset Nat

-- Initialize the game state
@[simp] def nr_game_init : NRGameState EncStateType := ⟨scheme.initial_state, {}⟩

-- The adversary calls this oracle with nonce n
@[simp] def nr_game_oracle (gs: NRGameState EncStateType) (n : Nat) :
    Bits × (NRGameState EncStateType) :=
  if n ∈ gs.used_nums then (rand, gs) -- adversary tried to cheat
  else
    let (enc_out, s) := scheme.enc_func gs.enc_state n
    (enc_out, {enc_state := s, used_nums := gs.used_nums ∪ {n} })

-- Security definition
@[simp] def is_nr_cpa : Prop :=
  ∃ (sec_invariant: NRGameState EncStateType → Prop),
      (sec_invariant (nr_game_init scheme)) ∧
      ∀ (gs: NRGameState EncStateType), sec_invariant gs →
        ∀ (n: Nat),
          (nr_game_oracle scheme gs n).1 = rand ∧
          sec_invariant (nr_game_oracle scheme gs n).2

-- The simple encryption scheme: n=nonce, prf(k,n) xor msg
@[simp] def enc_prf_nonce : EncryptionSchemeWithNonce PrfNumInputs :=
  {initial_state := (PrfNumInputs.new rand).1,
   enc_func := fun prf n => let (prf_out, prf_next) := prf.eval (num n)
                            (xor prf_out any, prf_next)}

-- Security proof
theorem is_nr_cpa_enc_prf_nonce: is_nr_cpa enc_prf_nonce := by
  use fun gs => gs.used_nums = gs.enc_state.used_nums -- security invariant
  aesop
