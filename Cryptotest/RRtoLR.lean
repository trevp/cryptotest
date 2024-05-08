
structure SymEnc (KeyType: Type) (MessageType: Type) (CiphertextType: Type) where
  init: Unit → KeyType
  enc: KeyType → MessageType → CiphertextType
  dec: KeyType → CiphertextType -> Option MessageType
  random: Unit -> CiphertextType


def game_real (s: SymEnc KeyType MessageType CiphertextType)
  (k: KeyType) (m : MessageType) : CiphertextType :=
  s.enc k m

def game_random (s: SymEnc KeyType MessageType CiphertextType)
  (_k: KeyType) (_m : MessageType) : CiphertextType :=
  s.random ()

def is_ror_ind (s: SymEnc KeyType MessageType CipherTextType) :=
  ∀ (k: KeyType) (m: MessageType), game_real s k m = game_random s k m


def game_lr_left (s: SymEnc KeyType MessageType CiphertextType)
  (k: KeyType) (ml : MessageType) (_mr : MessageType) : CiphertextType :=
  s.enc k ml

def game_lr_right (s: SymEnc KeyType MessageType CiphertextType)
  (k: KeyType) (_ml : MessageType) (mr : MessageType) : CiphertextType :=
  s.enc k mr

def is_lr_ind (s: SymEnc KeyType MessageType CipherTextType) :=
  ∀ (k: KeyType) (ml: MessageType) (mr: MessageType), game_lr_left s k ml mr = game_lr_right s k ml mr


theorem ror_implies_lr (s: SymEnc KeyType MessageType CipherTextType) :
    is_ror_ind s → is_lr_ind s := by
  -- simp_all [game_real, game_random, is_ror_ind, game_lr_left, game_lr_right, is_lr_ind, SymEnc]
  -- above works, but do it step-by-step for demonstration:
  intros h
  unfold is_lr_ind
  unfold game_lr_left
  unfold game_lr_right
  unfold is_ror_ind at h
  unfold game_real at h
  unfold game_random at h
  intro k ml mr
  have hl := h k ml
  have hr := h k mr
  rw [hl, hr]
