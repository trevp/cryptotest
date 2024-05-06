import Cryptotest.Basics
import Cryptotest.CryptoAlgs

def OneTimeIndAdversary : Type := Unit → Bits

def one_time_ind_game (a: OneTimeIndAdversary) (e: EncryptionAlgorithm) : Prop :=
  let m := a () -- Adversary chooses a message
  match m with
  | Bits.ind _ => true
  | Bits.any   => true
  | Bits.num _ =>       -- Adversary only allowed to query a message it knows (Bits.num)
    let (c, s) := e m IndState.initial
    c.is_indistinguishable s -- Game returns false if adversary wins

def is_one_time_ind (e: EncryptionAlgorithm) : Prop :=
     ∀ a: OneTimeIndAdversary, one_time_ind_game a e


