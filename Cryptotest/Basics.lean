import Mathlib
open Finset

-- BASICS -------------------------------------------------

structure IndState where ----------------------------------
  next_tag  : Nat
  used_tags : Finset Nat
  used_prf_tags : Finset Nat

namespace IndState
def get_next_tag (s: IndState) : Nat × IndState :=
  let t := s.next_tag
  (t, {s with next_tag := t + 1 })

def is_tag_unused (s: IndState) (t: Nat) : Bool :=
  t ∉ s.used_tags

def use_tag (s: IndState) (t: Nat) : IndState :=
  {s with used_tags := s.used_tags ∪ {t} }

def initial : IndState := {next_tag := 0, used_tags := {}, used_prf_tags := {}}
--
def is_well_formed (s: IndState) : Prop :=
  ∀t ∈ s.used_tags, t < s.next_tag

def is_not_earlier (s1: IndState) (s2: IndState) : Prop :=
  s1.next_tag >= s2.next_tag

def is_later (s1: IndState) (s2: IndState) : Prop :=
  s1.next_tag > s2.next_tag
end IndState

inductive Bits where --------------------------------------
  | any: Bits               -- any value
  | num (t: Nat): Bits      -- all possible values are numbered
  | rand (t: Nat): Bits     -- indistinguishable from random
  deriving Repr

namespace Bits
def new_rand (s: IndState) : Bits × IndState :=
  let (t, s) := s.get_next_tag
  (Bits.rand t, s)

def rng := new_rand

def consume_rand (b: Bits) (s: IndState) : IndState :=
  match b with
  | Bits.rand t => s.use_tag t
  | _ => s

def is_indistinguishable (b: Bits) (s: IndState) : Bool :=
  match b with
  | Bits.rand t => s.is_tag_unused t
  | _ => false

def is_non_colliding (b1: Bits) (b2: Bits) : Bool :=
  match b1, b2 with
  | Bits.rand t1, Bits.rand t2  => t1 ≠ t2
  | Bits.rand _, _  => true
  | _, Bits.rand _  => true
  | _, _           => false

def xor (b1: Bits) (b2: Bits) (s1: IndState) : Bits × IndState :=
  match b1, b2,
        b1.is_indistinguishable s1,
        b2.is_indistinguishable s1,
        Bits.is_non_colliding b1 b2 with
  | Bits.rand _,  Bits.rand _,    true,   true,   true     => Bits.new_rand (b2.consume_rand (b1.consume_rand s1))
  | Bits.rand _,  Bits.rand _,    true,   true,   false    => (Bits.any,   (b2.consume_rand (b1.consume_rand s1)))
  | Bits.rand _,   _,            true,   _,      _        => Bits.new_rand (b1.consume_rand s1)
  | _,            Bits.rand _,   _,      true,   _        => Bits.new_rand (b2.consume_rand s1)
  | _,            _,            _,      _,      _        => (Bits.any, s1)
---
def is_well_formed (b: Bits) (s: IndState) : Prop :=
  match b with
  | Bits.rand t => t < s.next_tag
  | _ => true

def is_parent (b: Bits) (s: IndState) : Prop :=
  match b with
  | Bits.rand t => t = s.next_tag
  | _ => false

end Bits

-- CRYPTO ALGS -------------------------------------------------

def EncryptionAlgorithm : Type := Bits → IndState → Bits × IndState

def enc_otp : EncryptionAlgorithm := fun (m: Bits) (s: IndState) =>
  let (k, s) := Bits.rng s
  let (c, s) := Bits.xor k m s
  (c, s)

def enc_double_otp : EncryptionAlgorithm := fun (m: Bits) (s: IndState) =>
  let (k, s) := Bits.rng s
  let (c, s) := Bits.xor k m s
  let (k, s) := Bits.rng s
  let (c, s) := Bits.xor k c s
  (c, s)

def enc_double_otp_reorder : EncryptionAlgorithm := fun (m: Bits) (s: IndState) =>
  let (k1, s) := Bits.rng s
  let (k2, s) := Bits.rng s
  let (c, s) := Bits.xor k1 m s
  let (c, s) := Bits.xor k2 c s
  (c, s)

---

def prf_rand (input : Bits) (s: IndState) : Bits × IndState :=
  match input with
  | Bits.rand t =>
    if t ∈ s.used_prf_tags then
      (Bits.any, s)
    else
      let (output, s) := Bits.new_rand s
      (output, {s with used_prf_tags := s.used_prf_tags ∪ {t} })
  | _ => (Bits.any, s)

def prf_enc : EncryptionAlgorithm := fun (m: Bits) (s: IndState) =>
  let (r, s) := Bits.rng s
  let (k, s) := prf_rand r s
  let (c, s) := Bits.xor k m s
  (c, s)

-- DEFINITIONS -------------------------------------------------

def OneTimeIndAdversary : Type := Unit → Bits

def one_time_ind_game (a: OneTimeIndAdversary) (e: EncryptionAlgorithm) : Prop :=
  let m := a () -- Adversary chooses a message
  match m with
  | Bits.rand _ => true
  | Bits.any   => true
  | Bits.num _ =>       -- Adversary only allowed to query a message it knows (Bits.num)
    let (c, s) := e m IndState.initial
    c.is_indistinguishable s -- Game returns false if adversary wins

def is_one_time_ind (e: EncryptionAlgorithm) : Prop :=
     ∀ a: OneTimeIndAdversary, one_time_ind_game a e

-- PROOFS -------------------------------------------------

lemma lemma_initial_is_well_formed : IndState.initial.is_well_formed := by
  unfold IndState.is_well_formed
  unfold IndState.initial
  simp

lemma lemma_well_formed_trans (s1: IndState) (s2: IndState) (b: Bits)
  (h1: b.is_well_formed s1)
  (h2: s2.is_not_earlier s1) :
    b.is_well_formed s2 := by
  revert h1
  unfold Bits.is_well_formed
  split
  rename_i t
  simp [IndState.is_not_earlier] at h2
  intro ht
  linarith
  simp

lemma lemma_is_not_earlier_rfl (s1: IndState) :
    s1.is_not_earlier s1 := by
  simp [IndState.is_not_earlier]

lemma lemma_is_not_earlier_trans (s3: IndState) (s2: IndState) (s1: IndState)
  (h1: s3.is_not_earlier s2)
  (h2: s2.is_not_earlier s1):
    s3.is_not_earlier s1 := by
  revert h1 h2
  simp [IndState.is_not_earlier]
  intro h1 h2
  linarith

lemma lemma_later_implies_not_earlier (s1: IndState) (s2: IndState)
  (h1: s1.is_later s2) :
    s1.is_not_earlier s2 := by
  simp [IndState.is_later] at h1
  simp [IndState.is_not_earlier]
  linarith

lemma lemma_parent_implies_non_colliding (s1 : IndState) (b1: Bits) (b2: Bits)
  (h1: b1.is_parent s1)
  (h2: b2.is_well_formed s1) :
    Bits.is_non_colliding b1 b2 := by
  simp [Bits.is_parent] at h1
  simp [Bits.is_well_formed] at h2
  unfold Bits.is_non_colliding
  cases hb1: b1
  case rand t1 =>
    cases hb2: b2
    case rand t2 =>
      aesop
    case num | any =>
      simp
  case num | any =>
    simp_all

lemma lemma_next_tag_unused (s: IndState)
  (h: s.is_well_formed) :
    s.next_tag ∉ s.used_tags := by
  simp [IndState.is_well_formed] at h
  contrapose h
  aesop

lemma lemma_get_next_tag_properties (s1: IndState) (sout: IndState)
  (h1: s1.is_well_formed)
  (h2: sout = s1.get_next_tag.2) :
    sout.is_well_formed ∧
    sout.is_later s1 := by
  simp [h2, IndState.get_next_tag]
  revert h1
  simp [IndState.is_well_formed]
  intro hlt
  apply And.intro
  · intros t ht
    specialize hlt t ht
    linarith
  · simp [IndState.is_later]

lemma lemma_consume_rand_properties (s1: IndState) (sout: IndState) (b: Bits)
  (h1: s1.is_well_formed)
  (h2: b.is_well_formed s1)
  (h3: sout = b.consume_rand s1) :
    sout.is_well_formed ∧
    sout.is_not_earlier s1 := by
  unfold IndState.is_well_formed IndState.is_not_earlier
  unfold IndState.is_well_formed at h1
  unfold Bits.is_well_formed at h2
  unfold Bits.consume_rand IndState.use_tag at h3
  aesop

lemma lemma_new_rand_properties
  (s1: IndState) (sout: IndState) (bout: Bits)
  (h1: s1.is_well_formed)
  (h2: (bout, sout) = Bits.new_rand s1) :
    sout.is_well_formed ∧
    sout.is_later s1 ∧
    bout.is_well_formed sout ∧
    bout.is_indistinguishable sout ∧
    bout.is_parent s1 := by
  simp [Bits.new_rand] at h2
  have hsoutp : _ := by
    exact lemma_get_next_tag_properties s1 sout h1 h2.2
  have hbout_wf: bout.is_well_formed sout := by
    rw [h2.1]
    rw [h2.2]
    simp [IndState.get_next_tag]
    unfold Bits.is_well_formed
    simp
  have hbout_ind: bout.is_indistinguishable sout := by
    rw [h2.1, h2.2]
    unfold Bits.is_indistinguishable
    unfold IndState.is_tag_unused
    simp
    apply lemma_next_tag_unused
    apply h1
  have hparent: bout.is_parent s1 := by
    unfold Bits.is_parent
    cases hbout: bout
    case rand t => aesop
    case num | any => aesop
  exact ⟨hsoutp.1, hsoutp.2, hbout_wf, hbout_ind, hparent⟩

lemma lemma_xor_ind_properties
  (s1: IndState) (sout: IndState) (b1: Bits) (b2: Bits)
  (h1: s1.is_well_formed)
  (h2: b1.is_well_formed s1)
  (h3: b2.is_well_formed s1)
  (h4: b1.is_indistinguishable s1 ∨ b2.is_indistinguishable s1)
  (h5: Bits.is_non_colliding b1 b2)
  (h6: (bout, sout) = Bits.xor b1 b2 s1) :
    sout.is_well_formed ∧
    sout.is_not_earlier s1 ∧
    bout.is_well_formed sout ∧
    bout.is_indistinguishable sout := by
  revert h6
  unfold Bits.xor
  split -- 5 cases - one for each branch of match
  · -- case 1:  both indistinguishable, noncolliding
    rename_i b1 b2 _ _ _ t1 t2 _ _ _
    intro h_out
    let s2 := Bits.consume_rand (Bits.rand t1) s1
    let s3 := Bits.consume_rand (Bits.rand t2) s2
    let s4 := (Bits.new_rand s3).2
    let b4 := (Bits.new_rand s3).1
    have hs2p : _ := by
      apply lemma_consume_rand_properties s1 s2 (Bits.rand t1) h1 h2
      simp [s2]
    have hs3p : _ := by
      apply lemma_consume_rand_properties s2 s3 (Bits.rand t2) hs2p.1
      apply lemma_well_formed_trans s1 s2 (Bits.rand t2) h3 hs2p.2
      simp [s3]
    have hs4p : _ := by
      apply lemma_new_rand_properties s3 s4 b4 hs3p.1
      simp [b4, s4]
    have _ : sout = s4 := by simp [s4, s3, s2]; rw [← h_out]
    have _ : bout = b4 := by simp [b4]; rw [← h_out]
    have _ : s4.is_not_earlier s3 := by
      apply lemma_later_implies_not_earlier s4 s3 hs4p.2.1
    aesop
  · -- case 2: both indistinguishable, colliding, contradicts input hypothesis
    aesop
  -- cases 3 and 4 are almost the same, so we factor out the commonality
  case' h_3 =>
    rename_i  b _ _ _ _ _ t _ _ _
  case' h_4 =>
    rename_i  b _ _ _ _ t _ _ _ _
  case h_3 | h_4 =>
    intro h_out
    let s2 := Bits.consume_rand (Bits.rand t) s1
    let s3 := (Bits.new_rand s2).2
    let b3 := (Bits.new_rand s2).1
    have hs2p : _ := by
      apply lemma_consume_rand_properties s1 s2 (Bits.rand t)
      assumption
      assumption
      simp [s2]
    have hs3p : _ := by
      apply lemma_new_rand_properties s2 s3 b3 hs2p.1
      simp [b3, s3]
    have _ : sout = s3 := by simp [s3, s2]; rw [← h_out]
    have _ : bout = b3 := by simp [b3]; rw [← h_out]
    have _ : s3.is_not_earlier s2 := by
      apply lemma_later_implies_not_earlier s3 s2 hs3p.2.1
    aesop
  · -- case 5: neither b1 nor b2 are indistinguishable, contradicts input hypothesis
    exfalso
    apply Or.elim h4 <;> simp [Bits.is_indistinguishable] <;> aesop

lemma lemma_otp_properties
  (s1: IndState) (sout: IndState) (m: Bits)
  (h1: s1.is_well_formed)
  (h2: m.is_well_formed s1)
  (h3: (bout, sout) = enc_otp m s1) :
    sout.is_well_formed ∧
    sout.is_not_earlier s1 ∧
    bout.is_well_formed sout ∧
    bout.is_indistinguishable sout := by
  let k := (Bits.new_rand s1).1
  let s2 := (Bits.new_rand s1).2
  let b3 := (Bits.xor k m s2).1
  let s3 := (Bits.xor k m s2).2
  have hs2p : _ := by
    apply lemma_new_rand_properties s1 s2 k h1
    simp [k, s2]
  have hnc: Bits.is_non_colliding k m := by
    apply lemma_parent_implies_non_colliding s1 k m hs2p.2.2.2.2 h2
  have hs3p :
      s3.is_well_formed ∧
      s3.is_not_earlier s2 ∧
      b3.is_well_formed s3 ∧
      b3.is_indistinguishable s3  := by
    apply lemma_xor_ind_properties s2 s3 k m hs2p.1 hs2p.2.2.1
    apply lemma_well_formed_trans s1 s2 m h2
    apply lemma_later_implies_not_earlier s2 s1 hs2p.2.1
    apply Or.inl hs2p.2.2.2.1
    exact hnc
    simp [b3, s3]
  have hbout : bout = b3 := by
    unfold enc_otp at h3
    unfold Bits.rng at h3
    simp at h3
    simp [b3, s2, k]
    rw [← h3]
  have hsout : sout = s3 := by
    unfold enc_otp at h3
    unfold Bits.rng at h3
    simp at h3
    simp [s3, s2, k]
    rw [← h3]
  rw [hbout, hsout]
  apply And.intro
  · apply hs3p.1
  · apply And.intro
    · apply lemma_is_not_earlier_trans s3 s2 s1 hs3p.2.1
      apply lemma_later_implies_not_earlier s2 s1 hs2p.2.1
    · apply hs3p.2.2

lemma lemma_double_otp_properties
  (s1: IndState) (sout: IndState) (m: Bits)
  (h1: s1.is_well_formed)
  (h2: m.is_well_formed s1)
  (h3: (bout, sout) = enc_double_otp m s1) :
    sout.is_well_formed ∧
    sout.is_not_earlier s1 ∧
    bout.is_well_formed sout ∧
    bout.is_indistinguishable sout := by

  let c2 := (enc_otp m s1).1
  let s2 := (enc_otp m s1).2
  have hs2p : _ := by
    apply lemma_otp_properties s1 s2 m h1 h2
    dsimp

  let c3 := (enc_otp c2 s2).1
  let s3 := (enc_otp c2 s2).2
  have hs3p : _ := by
    apply lemma_otp_properties s2 s3 c2 hs2p.1 hs2p.2.2.1
    dsimp

  have h_otp_equiv : enc_double_otp m s1 = enc_otp c2 s2 := by
    rfl
  rw [h_otp_equiv] at h3

  have hbout : bout = c3 := by
    simp [c3, s2, c2]
    rw [← h3]
  have hsout : sout = s3 := by
    simp [s3, s2, c2]
    rw [← h3]
  rw [hbout, hsout]
  apply And.intro
  · apply hs3p.1
  · apply And.intro
    · apply lemma_is_not_earlier_trans s3 s2 s1 hs3p.2.1 hs2p.2.1
    · apply And.intro
      · apply hs3p.2.2.1
      · apply hs3p.2.2.2

/-
lemma lemma_prf_enc_properties
  (s1: IndState) (sout: IndState) (m: Bits)
  (h1: s1.is_well_formed)
  (h2: m.is_well_formed s1)
  (h3: (bout, sout) = prf_enc m s1) :
    sout.is_well_formed ∧
    sout.is_not_earlier s1 ∧
    bout.is_well_formed sout ∧
    bout.is_indistinguishable sout := by
  unfold prf_enc at h3
  let (b4, s4) := (otp m s1)
  have h4: (b4, s4) = (otp m s1) := sorry
  unfold otp at h4
  split at h3
  unfold prf_rand at h3
  split at h3
  split at h3
  sorry
-/


-------------------------------------------------

theorem otp_is_one_time_ind : is_one_time_ind enc_otp := by
  unfold is_one_time_ind
  unfold one_time_ind_game
  intro a
  extract_lets m
  cases hm : m
  case rand _ | any =>
    simp
  case num _ =>
    simp
    let c := (enc_otp m IndState.initial).1
    let sout := (enc_otp m IndState.initial).2
    have otp_properties :
        sout.is_well_formed ∧
        sout.is_not_earlier IndState.initial ∧
        c.is_well_formed sout ∧
        c.is_indistinguishable sout := by
      apply lemma_otp_properties IndState.initial sout m
      apply lemma_initial_is_well_formed
      unfold Bits.is_well_formed
      unfold IndState.initial
      rw [hm]
      simp [sout]
    simp_all [c, sout]

theorem double_otp_is_one_time_ind : is_one_time_ind enc_double_otp := by
  unfold is_one_time_ind
  unfold one_time_ind_game
  intro a
  extract_lets m
  cases hm : m
  case rand _ | any =>
    simp
  case num _ =>
    simp
    let c := (enc_double_otp m IndState.initial).1
    let sout := (enc_double_otp m IndState.initial).2
    have double_otp_properties :
        sout.is_well_formed ∧
        sout.is_not_earlier IndState.initial ∧
        c.is_well_formed sout ∧
        c.is_indistinguishable sout := by
      apply lemma_double_otp_properties IndState.initial sout m
      apply lemma_initial_is_well_formed
      unfold Bits.is_well_formed
      unfold IndState.initial
      rw [hm]
      simp [sout]
    simp_all [c, sout]
