import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOddSymmetricCovering
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexOddPositiveHalfProjection_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricCovering.lean)
-/
@[path]
private lemma sixVertexOddPositiveHalfProjection_apply_eq
  {m : Nat}
  {p : Fin ((m + 1) + m) → Real}
  {j : Fin m} :
-- imply
  sixVertexOddPositiveHalfProjection m p j = p (sixVertexOddPositiveIndex m j) := by
-- proof
  apply StatMech.FrontierD.sixVertexOddPositiveHalfProjection_apply m p j

/--
[sixVertexOddPositiveHalfProjection_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricCovering.lean)
-/
@[path]
private lemma sixVertexOddPositiveHalfProjection_lift_eq
  {m : Nat}
  {q : Fin m → Real} :
-- imply
  sixVertexOddPositiveHalfProjection m (sixVertexOddSymmetricLift m q) = q := by
-- proof
  apply StatMech.FrontierD.sixVertexOddPositiveHalfProjection_lift m q

/--
[sixVertexOddSymmetricLift_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricCovering.lean)
-/
@[path]
private lemma sixVertexOddSymmetricLift_projection_eq
  {m : Nat}
  {p : Fin ((m + 1) + m) → Real}
-- given
  (hp : SixVertexRootSymmetric p) :
-- imply
  sixVertexOddSymmetricLift m (sixVertexOddPositiveHalfProjection m p) = p := by
-- proof
  apply StatMech.FrontierD.sixVertexOddSymmetricLift_projection m hp

/--
[isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_oddSymmetricJacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricCovering.lean)
-/
@[path]
private lemma isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_oddSymmetricJacobian_eq
  {a b : Real}
  {N m : Nat}
  {C : Set (SixVertexBetheContinuationSpace a b N ((m + 1) + m))}
-- given
  (ha : 2 < a)
  (hN : 0 < N)
  (hhalf : 2 * ((m + 1) + m) ≤ N)
  (hjac : ∀ z ∈ C, Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m z.1.1 (sixVertexOddPositiveHalfProjection m z.1.2))) :
-- imply
  IsLocalHomeomorphOn (@sixVertexBetheContinuationProjection a b N ((m + 1) + m)) C := by
-- proof
  apply StatMech.FrontierD.isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_oddSymmetricJacobian ha hN hhalf C hjac

/--
[isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_oddSymmetricJacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOddSymmetricCovering.lean)
-/
@[path]
private lemma isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_oddSymmetricJacobian_eq
  {a b : Real}
  {N m : Nat}
  {C : Set (SixVertexBetheContinuationSpace a b N ((m + 1) + m))}
-- given
  (ha : 2 < a)
  (hN : 0 < N)
  (hhalf : 2 * ((m + 1) + m) ≤ N)
  (hC : IsOpen C)
  (hjac : ∀ z ∈ C, Function.Injective (sixVertexOddSymmetricBetheRootJacobian N m z.1.1 (sixVertexOddPositiveHalfProjection m z.1.2))) :
-- imply
  IsLocalHomeomorph (sixVertexBetheContinuationProjectionOn C) := by
-- proof
  apply StatMech.FrontierD.isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_oddSymmetricJacobian ha hN hhalf C hC hjac


-- created on 2026-10-23
