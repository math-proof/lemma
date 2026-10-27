import Mathlib.Tactic


/--
heterogeneous/asymptotic equality
-/
def SEq {α : Type u} {Vector : α → Sort v} {n m : α} (a : Vector n) (b : Vector m) : Prop :=
  n = m ∧ HEq a b

