import «Cryptotest»

def test : Bool := Id.run do
  let s       := IndState.initial

  let m1      := Bits.num 1
  let m2      := Bits.any
  let (m3, s) := Bits.rng s
  if ¬ m3.is_indistinguishable s then 
    return false

  let (x1, s) := Bits.xor m1 m2 s -- Bits.any
  let (x2, s) := Bits.xor m2 m3 s -- Bits.ind
  let (x3, s) := Bits.xor m1 m3 s -- Bits.any (because m3 was consumed)

  if m3.is_indistinguishable s then 
    return false
  
  if match (x1, x2, x3) with 
  | (Bits.any, Bits.ind _, Bits.any) => true
  | _ => false then
    return true

  let (c1, s) := otp m1 s
  let (c2, s) := otp m2 s
  let (c3, s) := otp m3 s

  if (¬ c1.is_indistinguishable s) then 
    return false
  if (¬ c2.is_indistinguishable s) then 
    return false
  if (¬ c3.is_indistinguishable s) then 
    return false
  return true

#eval test



def main : IO Unit := do
  IO.println "Hello, otp is one time indistinguishable!"
