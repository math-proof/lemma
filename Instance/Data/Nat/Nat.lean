import Mathlib.Tactic
open Lean


instance : Coe Bool ℕ where
  coe b := b.toNat

instance [NatCast α] : Coe ℕ α where
  coe n := (n : α)

