import Mathlib
open Finset

structure IndState where ----------------------------------
  next_tag  : Nat
  used_tags : Finset Nat

namespace IndState
def get_next_tag (s: IndState) : Nat × IndState :=
  let t := s.next_tag
  (t, {s with next_tag := t + 1 })

def is_tag_unused (s: IndState) (t: Nat) : Bool :=
  t ∉ s.used_tags

def use_tag (s: IndState) (t: Nat) : IndState :=
  {s with used_tags := s.used_tags ∪ {t} }

def initial : IndState := {next_tag := 0, used_tags := {}}
--
def is_well_formed (s: IndState) : Prop :=
  ∀t ∈ s.used_tags, t < s.next_tag

def is_not_earlier (s1: IndState) (s2: IndState) : Prop :=
  s1.next_tag >= s2.next_tag

def is_later (s1: IndState) (s2: IndState) : Prop :=
  s1.next_tag > s2.next_tag
end IndState

inductive Bits where --------------------------------------
  | any: Bits              -- any value
  | num (n: Nat): Bits     -- all possible values are numbered
  | ind (t: Nat): Bits     -- indistinguishable from random
  deriving Repr

namespace Bits
def new_ind (s: IndState) : Bits × IndState :=
  let (t, s) := s.get_next_tag
  (Bits.ind t, s)

def rng := new_ind

def consume_ind (b: Bits) (s: IndState) : IndState :=
  match b with
  | Bits.ind t => s.use_tag t
  | _ => s

def is_indistinguishable (b: Bits) (s: IndState) : Bool :=
  match b with
  | Bits.ind t => s.is_tag_unused t
  | _ => false

def is_non_colliding (b1: Bits) (b2: Bits) : Bool :=
  match b1, b2 with
  | Bits.ind t1, Bits.ind t2  => t1 ≠ t2
  | Bits.ind _, _  => true
  | _, Bits.ind _  => true
  | _, _           => false

def xor (b1: Bits) (b2: Bits) (s1: IndState) : Bits × IndState :=
  match b1, b2,
        b1.is_indistinguishable s1,
        b2.is_indistinguishable s1,
        Bits.is_non_colliding b1 b2 with
  | Bits.ind _,  Bits.ind _,    true,   true,   true     => Bits.new_ind (b2.consume_ind (b1.consume_ind s1))
  | Bits.ind _,  Bits.ind _,    true,   true,   false    => (Bits.any,   (b2.consume_ind (b1.consume_ind s1)))
  | Bits.ind _,   _,            true,   _,      _        => Bits.new_ind (b1.consume_ind s1)
  | _,            Bits.ind _,   _,      true,   _        => Bits.new_ind (b2.consume_ind s1)
  | _,            _,            _,      _,      _        => (Bits.any, s1)
---
def is_well_formed (b: Bits) (s: IndState) : Prop :=
  match b with
  | Bits.ind t => t < s.next_tag
  | _ => true

def is_parent (b: Bits) (s: IndState) : Prop :=
  match b with
  | Bits.ind t => t = s.next_tag
  | _ => false

end Bits
