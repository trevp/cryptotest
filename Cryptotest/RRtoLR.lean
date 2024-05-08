
structure SymEnc (KeyType: Type) (MessageType: Type) (CiphertextType: Type) where
  init: Unit → KeyType
  enc: KeyType → MessageType → CiphertextType
  dec: KeyType → CiphertextType -> Option MessageType
  random: Unit -> CiphertextType


def oracle_real (s: SymEnc KeyType MessageType CiphertextType)
  (k: KeyType) (m : MessageType) : CiphertextType :=
  s.enc k m

def oracle_random (s: SymEnc KeyType MessageType CiphertextType)
  (_k: KeyType) (_m : MessageType) : CiphertextType :=
  s.random ()

def is_ror_ind (s: SymEnc KeyType MessageType CipherTextType) :=
  ∀ (k: KeyType) (m: MessageType), oracle_real s k m = oracle_random s k m


def oracle_left (s: SymEnc KeyType MessageType CiphertextType)
  (k: KeyType) (ml : MessageType) (_mr : MessageType) : CiphertextType :=
  s.enc k ml

def oracle_right (s: SymEnc KeyType MessageType CiphertextType)
  (k: KeyType) (_ml : MessageType) (mr : MessageType) : CiphertextType :=
  s.enc k mr

def is_lr_ind (s: SymEnc KeyType MessageType CipherTextType) :=
  ∀ (k: KeyType) (ml: MessageType) (mr: MessageType), oracle_left s k ml mr = oracle_right s k ml mr


theorem ror_implies_lr (s: SymEnc KeyType MessageType CipherTextType) :
    is_ror_ind s → is_lr_ind s := by
  -- simp_all [oracle_real, oracle_random, is_ror_ind, oracle_left, oracle_right, is_lr_ind, SymEnc]
  -- above works, but do it very explicitly for demonstration:
  intro h
  unfold is_lr_ind
  unfold oracle_left oracle_right
  unfold is_ror_ind at h
  unfold oracle_real oracle_random at h
  intro k ml mr
  have hl := h k ml
  have hr := h k mr
  rewrite [hl]
  rewrite [hr]
  rfl
