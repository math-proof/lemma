/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TotalDescentsParkingFunctions.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Instance.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring


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
