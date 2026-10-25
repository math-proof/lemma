import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.CylinderPathExpansion
open Finset Matrix StatMech StatMech.Ising


/--
[dot_mulVec_pow_eq_sum_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CylinderPathExpansion.lean)
-/
@[path]
private lemma dot_mulVec_pow_eq_sum_path_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R}
  {n : Nat}
-- given
  (ell a : E -> R) :
-- imply
  (∑ s, ell s * ((A ^ n) *ᵥ a) s) = ∑ q : Fin (n + 1) -> E, ell (q 0) * (∏ k : Fin n, A (q k.castSucc) (q k.succ)) * a (q (Fin.last n)) := by
-- proof
  apply StatMech.Ising.dot_mulVec_pow_eq_sum_path A ell a n

/--
[isingCylinderPartition_eq_sum_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/CylinderPathExpansion.lean)
-/
@[path]
private lemma isingCylinderPartition_eq_sum_path_eq
  [Fintype W]
  [DecidableEq W]
  [Nonempty W]
  {E : Finset (Sym2 W)}
  {n : Nat}
-- given
  (J : Sym2 W -> Real)
  (h Jvertical : W -> Real)
  (leftBoundary rightBoundary : ConfigSpace W -> Real) :
-- imply
  isingCylinderPartition E J h Jvertical leftBoundary rightBoundary n = ∑ q : Fin (n + 1) -> ConfigSpace W, Real.exp (rightBoundary (q 0) + leftBoundary (q (Fin.last n)) + (∑ k : Fin (n + 1), cylinderLayerInteraction E J h (q k)) + ∑ k : Fin n, cylinderInterLayerInteraction Jvertical (q k.castSucc) (q k.succ)) := by
-- proof
  apply StatMech.Ising.isingCylinderPartition_eq_sum_path E J h Jvertical leftBoundary rightBoundary n


-- created on 2026-10-23
