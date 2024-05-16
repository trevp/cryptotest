import Mathlib
open Finset

inductive IndExp where
  | any : IndExp                            -- could have any value
  | num (n: Nat) : IndExp                   -- n enumerates all possible values
  | rng : IndExp                            -- every occurrence is an independent random value
  | rng_pub : IndExp                        -- like above, but public to attacker (e.g. nonce)
  | prf (n: Nat) (i: IndExp) : IndExp       -- n indexes GlobalState.prfs, i is the PRF input
  | xor (i1: IndExp) (i2: IndExp) : IndExp  -- i1 and i2 are the operands being XOR'd together

structure GlobalState where
  prfs : List IndExp         -- append-only list of IndExp representing PRF keys

@[simp]
def initial_state : GlobalState := {prfs:=[]}

namespace GlobalState

@[simp]
def make_prf (gs: GlobalState) (i: IndExp) : (Nat × GlobalState) :=
  (gs.prfs.length, {gs with prfs := gs.prfs ++ [i] })

end GlobalState

namespace IndExp

@[simp]
def is_nonrepeating_random_rec (i: IndExp) (gs: GlobalState) : Prop :=
  match i with
  | any       => False
  | num _     => False
  | rng       => True
  | rng_pub   => True
  | prf n i   => match gs.prfs[n]? with
    | some _    => i.is_nonrepeating_random_rec gs
    | none      => False
  | xor i1 i2  => i1.is_nonrepeating_random_rec gs ∨ i2.is_nonrepeating_random_rec gs

@[simp] -- Indistinguishable from random?
def is_ind_rand_rec (i: IndExp) (gs: GlobalState) : Prop :=
  match i with
  | any       => False
  | num _     => False
  | rng       => True
  | rng_pub   => False
  | prf n i   => match gs.prfs[n]? with
    | some _    => i.is_nonrepeating_random_rec gs
    | none      => False
  | xor i1 i2  => i1.is_ind_rand_rec gs ∨ 
                  i2.is_ind_rand_rec gs

@[simp]
def is_ind_rand (i: IndExp) (gs: GlobalState) : Prop :=
  is_ind_rand_rec i gs ∧
  gs.prfs.foldr (fun (i': IndExp) (r: Prop) => i'.is_ind_rand_rec gs ∧ r) True

@[simp]
def is_ind_self (i: IndExp) (gs: GlobalState) : Prop :=
  match i with
  | any       => False
  | num _     => True
  | rng       => True
  | rng_pub   => True
  | _         => i.is_ind_rand gs


end IndExp



-- CRYPTO ALGS

open IndExp

-- Simple examples: Stateless one-time encryption:

def enc_otp : IndExp :=
  xor rng any

theorem enc_otp_is_ind_rand :
  enc_otp.is_ind_rand initial_state := by simp_all

def enc_double_otp : IndExp :=
  xor rng (xor rng any)

theorem enc_double_otp_is_ind_rand :
  enc_double_otp.is_ind_rand initial_state := by simp_all


-- Encryption algorithms for CPA security:
-- The function returns a GlobalState and an encryption function
-- The encryption function returns (IndExp, GlobalState)

def EncryptionAlgorithmCPA : Type := Unit → (GlobalState → IndExp × GlobalState) × GlobalState

@[simp]
def is_one_time_ind (alg: EncryptionAlgorithmCPA) : Prop :=
  let (enc, gs1) := alg ()
  let (c, gs2) := enc gs1
  c.is_ind_self gs2

@[simp]
def is_cpa (alg: EncryptionAlgorithmCPA) : Prop :=
  let (enc, gs1) := alg ()
  let (c, gs2) := enc gs1
  c.is_ind_self gs2

@[simp]
def enc_prf_random_nonce : EncryptionAlgorithmCPA := fun _ =>
  let (k, gs) := initial_state.make_prf rng
  let enc := fun gs' => (xor any (prf k rng_pub), gs')
  (enc, gs)

theorem enc_prf_random_nonce_is_one_time_ind : 
  is_one_time_ind (enc_prf_random_nonce) := by simp_all

theorem enc_prf_random_nonce_is_cpa : 
  is_cpa (enc_prf_random_nonce) := by simp_all
