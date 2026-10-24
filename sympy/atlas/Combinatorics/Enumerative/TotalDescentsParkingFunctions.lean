/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TotalDescentsParkingFunctions.lean -/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import sympy.atlas.Combinatorics.Enumerative.ParkingFunction
import Lemma.Finset.Enumerative.ParkingFunction
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-! # Total descents over all parking functions
-/
/-! ## Helpers for the Pollak circle argument and descent counting -/

/-- Circle embedding of a preference function. -/
private def emb (n : ℕ) (f : Fin n → Fin n) : Fin n → ZMod (n + 1) :=
  fun i => ((f i).val : ZMod (n + 1))

/-- Simultaneous rotation of all preferences on the circle. -/
private def shift (n : ℕ) (a : Fin n → ZMod (n + 1)) (c : ZMod (n + 1)) :
    Fin n → ZMod (n + 1) :=
  fun i => a i + c

private def pfSet (n : ℕ) : Finset (Fin n → Fin n) :=
  Finset.univ.filter (IsParkingFunction n)

-- descent predicate for one adjacent pair
private abbrev descentPair (n : ℕ) (f : Fin n → Fin n) (p : Fin n × Fin n) : Prop :=
  p.2.1 = p.1.1 + 1 ∧ f p.1 > f p.2

private abbrev adjPairs (n : ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p : Fin n × Fin n => p.2.1 = p.1.1 + 1)

private abbrev fiber (n : ℕ) (p : Fin n × Fin n) : Finset (Fin n → Fin n) :=
  (pfSet n).filter (fun f => descentPair n f p)
end MetaMathlibExt
