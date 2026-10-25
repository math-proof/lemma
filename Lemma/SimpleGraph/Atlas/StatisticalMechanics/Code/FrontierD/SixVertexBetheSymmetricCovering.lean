import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricCovering
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexEvenPositiveHalfProjection_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricCovering.lean)
-/
@[path]
private lemma sixVertexEvenPositiveHalfProjection_apply_eq
  {m : Nat}
  {p : Fin (m + m) → Real}
  {j : Fin m} :
-- imply
  sixVertexEvenPositiveHalfProjection m p j = p (Fin.natAdd m j) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenPositiveHalfProjection_apply m p j

/--
[sixVertexEvenPositiveHalfProjection_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricCovering.lean)
-/
@[path]
private lemma sixVertexEvenPositiveHalfProjection_lift_eq
  {m : Nat}
  {q : Fin m → Real} :
-- imply
  sixVertexEvenPositiveHalfProjection m (sixVertexEvenSymmetricLift m q) = q := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenPositiveHalfProjection_lift m q

/--
[sixVertexEvenSymmetricLift_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricCovering.lean)
-/
@[path]
private lemma sixVertexEvenSymmetricLift_projection_eq
  {m : Nat}
  {p : Fin (m + m) → Real}
-- given
  (hp : SixVertexRootSymmetric p) :
-- imply
  sixVertexEvenSymmetricLift m (sixVertexEvenPositiveHalfProjection m p) = p := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenSymmetricLift_projection m hp

/--
[isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_evenSymmetricJacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricCovering.lean)
-/
@[path]
private lemma isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_evenSymmetricJacobian_eq
  {a b : Real}
  {N m : Nat}
  {C : Set (SixVertexBetheContinuationSpace a b N (m + m))}
-- given
  (ha : 2 < a)
  (hN : 0 < N)
  (hhalf : 2 * (m + m) ≤ N)
  (hjac : ∀ z ∈ C, Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1 (sixVertexEvenPositiveHalfProjection m z.1.2))) :
-- imply
  IsLocalHomeomorphOn (@sixVertexBetheContinuationProjection a b N (m + m)) C := by
-- proof
  apply StatMech.FrontierD.isLocalHomeomorphOn_sixVertexBetheContinuationProjection_of_evenSymmetricJacobian ha hN hhalf C hjac

/--
[exists_sixVertexContinuousEvenSymmetricBetheBranch_of_jacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricCovering.lean)
-/
@[path]
private lemma exists_sixVertexContinuousEvenSymmetricBetheBranch_of_jacobian_eq
  {a b c₀ : Real}
  {N m : Nat}
  {z₀ : SixVertexBetheContinuationSpace a b N (m + m)}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hN : 0 < N)
  (hhalf : 2 * (m + m) ≤ N)
  (hjac : ∀ z ∈ sixVertexBetheContinuationSet a b N (m + m), Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m z.1 (sixVertexEvenPositiveHalfProjection m z.2)))
  (hz₀ : sixVertexBetheContinuationProjection z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin (m + m) → Real), roots c₀ = z₀.1.2 ∧ ∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexContinuousEvenSymmetricBetheBranch_of_jacobian ha hab hc₀ hN hhalf hjac z₀ hz₀

/--
[isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_evenSymmetricJacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricCovering.lean)
-/
@[path]
private lemma isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_evenSymmetricJacobian_eq
  {a b : Real}
  {N m : Nat}
  {C : Set (SixVertexBetheContinuationSpace a b N (m + m))}
-- given
  (ha : 2 < a)
  (hN : 0 < N)
  (hhalf : 2 * (m + m) ≤ N)
  (hC : IsOpen C)
  (hjac : ∀ z ∈ C, Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1 (sixVertexEvenPositiveHalfProjection m z.1.2))) :
-- imply
  IsLocalHomeomorph (sixVertexBetheContinuationProjectionOn C) := by
-- proof
  apply StatMech.FrontierD.isLocalHomeomorph_sixVertexBetheContinuationProjectionOn_of_evenSymmetricJacobian ha hN hhalf C hC hjac

/--
[exists_sixVertexContinuousEvenSymmetricBetheBranch_of_regularComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricCovering.lean)
-/
@[path]
private lemma exists_sixVertexContinuousEvenSymmetricBetheBranch_of_regularComponent_eq
  {a b c₀ : Real}
  {N m : Nat}
  {C : Set (SixVertexBetheContinuationSpace a b N (m + m))}
  {z₀ : C}
-- given
  (ha : 2 < a)
  (hab : a ≤ b)
  (hc₀ : c₀ ∈ Set.Icc a b)
  (hN : 0 < N)
  (hhalf : 2 * (m + m) ≤ N)
  (hCopen : IsOpen C)
  (hCcompact : IsCompact C)
  (hjac : ∀ z ∈ C, Function.Injective (sixVertexEvenSymmetricBetheRootJacobian N m z.1.1 (sixVertexEvenPositiveHalfProjection m z.1.2)))
  (hz₀ : sixVertexBetheContinuationProjectionOn C z₀ = ⟨c₀, hc₀⟩) :
-- imply
  ∃ roots : C(Real, Fin (m + m) → Real), roots c₀ = z₀.1.1.2 ∧ ∀ t ∈ Set.Icc a b, SixVertexSatisfiesBetheEquations t N (m + m) (roots t) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexContinuousEvenSymmetricBetheBranch_of_regularComponent ha hab hc₀ hN hhalf C hCopen hCcompact hjac z₀ hz₀


-- created on 2026-10-23
