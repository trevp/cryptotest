import Mathlib
open Finset

-- Bits is a fixed-length sequence of bits of cryptographic length, e.g. 128 or 256 bits.
inductive Bits where
  | any           : Bits     -- any value
  | rand          : Bits     -- indistinguishable from random
  | rand_pub      : Bits     -- indistinguishable from random but public (e.g. nonce)
  | num (n: Nat)  : Bits     -- integer encoded into bits

@[simp] def bits_xor (b1: Bits) (b2: Bits) : Bits :=
  match b1, b2 with
  | Bits.rand, _ => Bits.rand -- XOR of anything with random is random
  | _, Bits.rand => Bits.rand
  | _, _      => Bits.any     -- Otherwise "any"

@[simp] instance : Add Bits where add := bits_xor -- overload "+" operator

inductive PrfRandInputs where -- PRF for rand and rand_pub inputs
  | good_key: PrfRandInputs
  | bad_key: PrfRandInputs

namespace PrfRandInputs

@[simp] def new : Bits → PrfRandInputs
  | Bits.rand => PrfRandInputs.good_key
  | _ => PrfRandInputs.bad_key

@[simp] def eval (prf: PrfRandInputs) (b: Bits) : Bits × PrfRandInputs :=
  match prf, b with
  | PrfRandInputs.good_key, Bits.rand |
    PrfRandInputs.good_key, Bits.rand_pub => (Bits.rand, prf)
  | _, _ => (Bits.any, prf)

end PrfRandInputs

inductive PrfNumInputs where -- PRF for num inputs
  | good_key (used_nums: Finset Nat) : PrfNumInputs
  | bad_key : PrfNumInputs

namespace PrfNumInputs

@[simp] def new : Bits → PrfNumInputs
  | Bits.rand => PrfNumInputs.good_key {}
  | _ => PrfNumInputs.bad_key

@[simp] def eval (prf: PrfNumInputs) (b: Bits) : Bits × PrfNumInputs :=
  match prf, b with
  | PrfNumInputs.good_key used_nums, Bits.num n =>
    if n ∉ used_nums then (Bits.rand, PrfNumInputs.good_key (used_nums ∪ {n}))
    else (Bits.any, prf)
  | _, _ => (Bits.any, prf)

end PrfNumInputs

-- Simple proofs: Encryption with One-Time Pad
----------------------------------------------
@[simp] def enc_otp         : Bits := Bits.rand + Bits.any
@[simp] def enc_double_otp  : Bits := Bits.rand + (Bits.rand + Bits.any)

theorem is_ind_enc_otp        : enc_otp = Bits.rand        := by rfl
theorem is_ind_enc_double_otp : enc_double_otp = Bits.rand := by rfl

-- CPA security of simple PRF encryption scheme
-----------------------------------------------
structure EncryptionScheme (EncState: Type) where
  new : Bits → EncState              -- initialize with a key
  enc : EncState → (Bits × EncState) -- encrypt Bits.any, update state

-- Security definition
@[simp] def is_cpa (scheme: EncryptionScheme EncState) : Prop :=
  ∃ (invariant: EncState → Prop), invariant (scheme.new Bits.rand) ∧
    ∀ (enc_state: EncState), invariant enc_state →
      let (ciphertext, updated_enc_state) := scheme.enc enc_state
      ciphertext = Bits.rand ∧ invariant updated_enc_state

-- The simple encryption scheme: r=rand_pub, prf(key,r) xor msg
@[simp] def enc_prf_random : EncryptionScheme PrfRandInputs :=
  {new := fun key =>  PrfRandInputs.new key,
   enc := fun prf =>  let r := Bits.rand_pub;
                      let msg := Bits.any
                      let (prf_output, updated_prf) := prf.eval r;
                      (prf_output + msg, updated_prf)}

-- Security proof
theorem is_cpa_enc_prf_random: is_cpa enc_prf_random := by
  use fun enc_state =>    -- invariant
    match enc_state with
      | PrfRandInputs.good_key => True
      | PrfRandInputs.bad_key => False
  aesop

-- CPA security of nonce-based PRF encryption scheme
-- Adversary allowed to choose nonces n, but can't reuse them.
-- Similar to Easycrypt: https://fdupress.gitlab.io/easycrypt-web/
--------------------------------------------------------------
structure EncryptionSchemeWithNonce (EncState: Type) where
  new : Bits → EncState                    -- initialize with a key
  enc : EncState → Nat → (Bits × EncState) -- encrypt Bits.any with nonce, update state

-- The adversary interacts with a stateful game:
structure NRGameState (EncState: Type) where
  enc_state : EncState
  used_nums : Finset Nat

-- Initialize the game state
@[simp] def nr_game_init (scheme: EncryptionSchemeWithNonce EncState) :
    NRGameState EncState :=
  ⟨scheme.new Bits.rand, {}⟩

-- The adversary calls this oracle with nonce n
@[simp] def nr_game_oracle (scheme: EncryptionSchemeWithNonce EncState)
  (gs: NRGameState EncState) (n : Nat) :
    Bits × (NRGameState EncState) :=
  if n ∈ gs.used_nums then (Bits.rand, gs) -- adversary tried to cheat
  else
    let (ciphertext, updated_enc_state) := scheme.enc gs.enc_state n
    (ciphertext, {enc_state := updated_enc_state, used_nums := gs.used_nums ∪ {n} })

-- Security definition
@[simp] def is_nr_cpa (scheme: EncryptionSchemeWithNonce EncState) : Prop :=
  ∃ (invariant: NRGameState EncState → Prop), invariant (nr_game_init scheme) ∧
    ∀ (game_state: NRGameState EncState) (n: Nat), invariant game_state →
      let (ciphertext, updated_game_state) := (nr_game_oracle scheme game_state n);
      ciphertext = Bits.rand ∧ invariant updated_game_state

-- The simple encryption scheme: n=nonce, prf(k,n) xor msg
@[simp] def enc_prf_nonce : EncryptionSchemeWithNonce PrfNumInputs :=
  {new := fun key => PrfNumInputs.new key,
   enc := fun prf n =>  let (prf_output, updated_prf) := prf.eval (Bits.num n);
                        (prf_output + Bits.any, updated_prf)}

-- Security proof
theorem is_nr_cpa_enc_prf_nonce: is_nr_cpa enc_prf_nonce := by
  use fun game_state => -- invariant
    match game_state.enc_state with
    | PrfNumInputs.good_key used_nums => game_state.used_nums = used_nums
    | PrfNumInputs.bad_key => False
  aesop

-- Public-key crypto and DH
---------------------------
inductive GroupElement where
  | any           : GroupElement     -- any value
  | rand          : GroupElement     -- indistinguishable from random
  | rand_pub      : GroupElement     -- indistinguishable from random but public (e.g. nonce)
  | entropy       : GroupElement     -- high entropy but not necessarily uniform

@[simp] def group_element_add (e1: GroupElement) (e2: GroupElement) :=
  match e1, e2 with
  | GroupElement.rand, _  => GroupElement.rand
  | _, GroupElement.rand  => GroupElement.rand
  | _, _                  => GroupElement.any

@[simp] instance : Add GroupElement where
  add := group_element_add -- overload "+" operator

@[simp] def hash_to_bits: GroupElement → Bits -- treat as a random oracle
  | GroupElement.rand | GroupElement.entropy => Bits.rand
  | _ => Bits.any

@[simp] def ddh_triple: (GroupElement × GroupElement × GroupElement) :=
  (GroupElement.rand_pub, GroupElement.rand_pub, GroupElement.rand)

@[simp] def cdh_triple: (GroupElement × GroupElement × GroupElement) :=
  (GroupElement.rand_pub, GroupElement.rand_pub, GroupElement.entropy)

-- Simple proofs: ElGamal and Hashed ElGamal Encryption
--------------------------------------------------------
@[simp] def elgamal_ddh: GroupElement :=
  let (_pub_key, _pub_ephemeral, shared_secret) := ddh_triple
  shared_secret + GroupElement.any

@[simp] def hashed_elgamal_ddh: Bits :=
  let (_pub_key, _pub_ephemeral, shared_secret) := ddh_triple
  (hash_to_bits shared_secret) + Bits.any

@[simp] def hashed_elgamal_cdh: Bits :=
  let (_pub_key, _pub_ephemeral, shared_secret) := cdh_triple
  (hash_to_bits shared_secret) + Bits.any

theorem is_one_time_ind_elgamal_ddh : elgamal_ddh = GroupElement.rand := by rfl
theorem is_one_time_ind_hashed_elgamal_ddh : hashed_elgamal_ddh = Bits.rand := by rfl
theorem is_one_time_ind_hashed_elgamal_cdh : hashed_elgamal_cdh = Bits.rand := by rfl

-- Hybrid encryption - Use DH to key an encryption scheme
---------------------------------------------------------
@[simp] def hybrid_dh_encryption_cdh (scheme: EncryptionScheme EncState) : Bits :=
  let (_pub_key, _pub_ephemeral, shared_secret) := cdh_triple
  let (ciphertext, _) := scheme.enc (scheme.new (hash_to_bits shared_secret))
  ciphertext

theorem is_one_time_ind_hybrid_dh_encryption_cdh
  (scheme: EncryptionScheme EncState) (h_scheme: is_cpa scheme) :
    hybrid_dh_encryption_cdh scheme = Bits.rand := by aesop
