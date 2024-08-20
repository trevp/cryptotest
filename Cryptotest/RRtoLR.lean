import Mathlib

structure SymEnc (KeyType: Type) (MessageType: Type) (CiphertextType: Type) where
  init: Unit → KeyType
  enc: KeyType → MessageType → CiphertextType
  dec: KeyType → CiphertextType → Option MessageType
  random: Unit → CiphertextType

@[simp] def oracle_real (s: SymEnc KeyType MessageType CiphertextType)
  (k: KeyType) (m : MessageType) : CiphertextType :=
  s.enc k m

@[simp] def oracle_random (s: SymEnc KeyType MessageType CiphertextType)
  (_k: KeyType) (_m : MessageType) : CiphertextType :=
  s.random ()

@[simp] def is_ror_ind (s: SymEnc KeyType MessageType CipherTextType) :=
  ∀ (k: KeyType) (m: MessageType), oracle_real s k m = oracle_random s k m


@[simp] def oracle_left (s: SymEnc KeyType MessageType CiphertextType)
  (k: KeyType) (ml : MessageType) (_mr : MessageType) : CiphertextType :=
  s.enc k ml

@[simp] def oracle_right (s: SymEnc KeyType MessageType CiphertextType)
  (k: KeyType) (_ml : MessageType) (mr : MessageType) : CiphertextType :=
  s.enc k mr

@[simp] def is_lr_ind (s: SymEnc KeyType MessageType CipherTextType) :=
  ∀ (k: KeyType) (ml: MessageType) (mr: MessageType), oracle_left s k ml mr = oracle_right s k ml mr

-- 3 proof examples:

theorem ror_implies_lr_proof_1 (s: SymEnc KeyType MessageType CipherTextType) :
    is_ror_ind s → is_lr_ind s := by aesop

theorem ror_implies_lr_proof_2 (s: SymEnc KeyType MessageType CipherTextType) :
    is_ror_ind s → is_lr_ind s := by
  intro h
  unfold is_lr_ind
  unfold oracle_left oracle_right
  unfold is_ror_ind at h
  unfold oracle_real oracle_random at h
  intro k ml mr
  have hl : s.enc k ml = s.random () := h k ml
  have hr : s.enc k mr = s.random () := h k mr
  rw [hl]
  rw [hr]

-- rewriting above in "calc" style, not that interesting...
theorem ror_implies_lr_proof_3 (s: SymEnc KeyType MessageType CipherTextType) :
    is_ror_ind s → is_lr_ind s := by
  intro h
  unfold is_lr_ind
  unfold oracle_left oracle_right
  unfold is_ror_ind at h
  unfold oracle_real oracle_random at h
  intro k ml mr
  -- prove goal: ∀ k ml mlr, s.enc k ml = s.enc k mr
  -- using h:    ∀ k m, s.enc k m = s.random ()
  calc s.enc k ml = s.random () := by rw [(h k ml)]
                _ = s.enc k mr  := by rw [←(h k mr)]
