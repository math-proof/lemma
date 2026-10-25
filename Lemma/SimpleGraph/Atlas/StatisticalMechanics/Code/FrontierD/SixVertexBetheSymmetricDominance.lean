import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricDominance
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexEvenSymmetricBetheRootJacobian_injective_of_sourceBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricDominance.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricBetheRootJacobian_injective_of_sourceBounds_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m → Real}
  {G : Fin m → Real}
  {eps M : Real}
-- given
  (hc : 2 < c)
  (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (heps : 0 ≤ eps)
  (hM : 0 ≤ M)
  (hmargin : M + 2 * eps < 2 * Real.pi)
  (hdiag : ∀ j, |sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j - 2 * Real.pi| ≤ eps)
  (hoff : ∀ j, |(∑ k ∈ Finset.univ.erase j, sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) - G j| ≤ eps)
  (hG : ∀ j, 0 ≤ G j ∧ G j ≤ M) :
-- imply
  Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m c q) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricBetheRootJacobian_injective_of_sourceBounds hc q hq G eps M heps hM hmargin hdiag hoff hG


-- created on 2026-10-23
