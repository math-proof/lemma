/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TotalDescentsParkingFunctions.lean -/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Instance.Combinatorics.Enumerative.ParkingFunction
public import Theorem.Finset.Enumerative.ParkingFunction
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

/-! # Total descents over all parking functions
-/
/-! ## Helpers for the Pollak circle argument and descent counting -/

/-- Circle embedding of a preference function. -/
def emb (n : ℕ) (f : Fin n → Fin n) : Fin n → ZMod (n + 1) :=
  fun i => ((f i).val : ZMod (n + 1))

/-- Simultaneous rotation of all preferences on the circle. -/
def shift (n : ℕ) (a : Fin n → ZMod (n + 1)) (c : ZMod (n + 1)) :
    Fin n → ZMod (n + 1) :=
  fun i => a i + c

def pfSet (n : ℕ) : Finset (Fin n → Fin n) :=
  Finset.univ.filter (IsParkingFunction n)

end MetaMathlibExt
