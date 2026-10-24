import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Probability.FiniteWitnessUnionBound
open Finset Set StatMech StatMech.Probability


/--
[finiteEventMass_tail_le_choose_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/FiniteWitnessUnionBound.lean)
-/
@[path]
private lemma finiteEventMass_tail_le_choose_mul_pow_eq
  [Fintype Omega]
  {a : Real}
-- given
  (mu : Omega -> Real)
  (hmu : forall omega, 0 <= mu omega)
  (K : Omega -> Nat)
  (h n : Nat)
  (Witness : Finset (Fin h) -> Omega -> Prop)
  (hcover : forall omega, n <= K omega -> exists S : Finset (Fin h), S.card = n /\ Witness S omega)
  (hmass : forall S : Finset (Fin h), S.card = n -> finiteEventMass mu {omega | Witness S omega} <= a ^ n) :
-- imply
  finiteEventMass mu {omega | n <= K omega} <= Nat.choose h n * a ^ n := by
-- proof
  apply StatMech.Probability.finiteEventMass_tail_le_choose_mul_pow mu hmu K h n a Witness hcover hmass


-- created on 2026-10-23
