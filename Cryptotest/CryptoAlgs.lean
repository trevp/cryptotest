import Cryptotest.Basics

def EncryptionAlgorithm : Type := Bits → IndState → Bits × IndState

def otp : EncryptionAlgorithm := fun (m: Bits) (s: IndState) =>
  let (k, s) := Bits.rng s
  Bits.xor k m s

