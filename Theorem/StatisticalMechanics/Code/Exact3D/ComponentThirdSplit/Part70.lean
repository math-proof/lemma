/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part73
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    0 ≤
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
        β H n Ω v := by
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
  exact Finset.sum_nonneg fun R _hR =>
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
      hβ hH n Ω v
      (finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true ∪ R)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution_eq_unmarkedOptions_singleton_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
        β H n Ω v =
      ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
  exact
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet_one_sum_eq_unmarkedOptions_singleton_sum
      v
      (fun R =>
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true ∪
            R))

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution_le_unmarkedOptions_singletonBudget_sum
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {B : Option (FK.boxVerts 3 n) → ℝ}
    (hB :
      ∀ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
          B x) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
        β H n Ω v ≤
      ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v, B x := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution_eq_unmarkedOptions_singleton_sum]
  exact Finset.sum_le_sum fun x hx => hB x hx

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembership_unmarkedOptions_singletonBudget_sum_le_card_mul_of_le
    {n : ℕ} {v : FK.boxVerts 3 n}
    {B : Option (FK.boxVerts 3 n) → ℝ} {b : ℝ}
    (hB :
      ∀ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
        B x ≤ b) :
    (∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v, B x) ≤
      ((finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v).card : ℝ) *
        b := by
  have hsum :
      (∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v, B x) ≤
        ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v, b := by
    exact Finset.sum_le_sum fun x hx => hB x hx
  simpa [Finset.sum_const, nsmul_eq_mul] using hsum

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_residualSetContribution_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v =
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
        β H n Ω v := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_one_of_boundary
      β H n Ω hv]
  unfold
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_eq_unmarkedResidualExactCardSet_sum
      β H n Ω v true true true 1

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution_eq_labelFreeRawFourShare_one_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
        β H n Ω v =
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω true true true 1 := by
  calc
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution
        β H n Ω v =
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v := by
        exact
          (finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_residualSetContribution_of_boundary
            β H n Ω hv).symm
    _ =
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawFourShare
        v β H Ω true true true 1 :=
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_labelFreeRawFourShare_one_of_boundary
          β H n Ω hv

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_sourceSupport_unmarkedResidualCard_one_sum_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v =
      ∑ S ∈
        (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v).filter
          (fun S =>
            finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
                finiteBoundaryGhostSourceClassEndpointMembershipLabel
                  SourceClassCardinalityCase.fourPlus
                  true true true ∧
              (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
                1),
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_one_of_boundary
      β H n Ω hv]
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_true_true_true_eq_sourceClassSupport_endpointMembership_fourPlus_unmarkedResidualCard_sum_of_boundary_of_mem_Icc_one
      β H n Ω v hv
      (Finset.mem_Icc.mpr
        ⟨le_rfl,
          finiteBoundaryGhostSourceClassEndpointMembership_one_le_box_volume_sub_two_of_boundary
            hv⟩)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_unmarkedOptions_singleton_sum_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v =
      ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_residualSetContribution_of_boundary
      β H n Ω hv]
  exact
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneResidualSetContribution_eq_unmarkedOptions_singleton_sum
      β H n Ω v

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_le_unmarkedOptions_singletonBudget_sum_of_boundary
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {singletonBudget : Option (FK.boxVerts 3 n) → ℝ}
    (hpoint :
      ∀ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
          singletonBudget x) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v ≤
      ∑ x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v,
        singletonBudget x := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_unmarkedOptions_singleton_sum_of_boundary
      β H n Ω hv]
  exact Finset.sum_le_sum fun x hx => hpoint x hx

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_singletonOptionNonemptyClassifiedSet_sum_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v =
      ∑ x ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
          v Ω true true true,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) := by
  classical
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ω true true true
  let unmarkedOptions := finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v
  let f : Option (FK.boxVerts 3 n) → ℝ :=
    fun x =>
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v
        (finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true ∪
          ({x} : Finset (Option (FK.boxVerts 3 n))))
  have hlive_subset : liveOptions ⊆ unmarkedOptions := by
    intro x hx
    exact
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet_mem_iff.mp
        hx).1
  have hsum_live :
      (∑ x ∈ unmarkedOptions, f x) = ∑ x ∈ liveOptions, f x := by
    refine (Finset.sum_subset hlive_subset ?_).symm
    intro x hxUnmarked hxNotLive
    have hnotNonempty :
        ¬
          (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω true true true
            ({x} : Finset (Option (FK.boxVerts 3 n)))).Nonempty := by
      intro hnonempty
      exact hxNotLive
        ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet_mem_iff).mpr
          ⟨hxUnmarked, hnonempty⟩)
    have hempty :
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω true true true
            ({x} : Finset (Option (FK.boxVerts 3 n))) =
          ∅ := by
      exact Finset.not_nonempty_iff_eq_empty.mp hnotNonempty
    dsimp [f]
    rw [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_sum_classifiedSet
        β H n Ω v true true true
        ({x} : Finset (Option (FK.boxVerts 3 n)))]
    simp [hempty]
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_unmarkedOptions_singleton_sum_of_boundary
      β H n Ω hv]
  simpa [liveOptions, unmarkedOptions, f] using hsum_live

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_le_singletonOptionNonemptyClassifiedSet_singletonBudget_sum_of_boundary
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {singletonBudget : Option (FK.boxVerts 3 n) → ℝ}
    (hpoint :
      ∀ x ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
            v Ω true true true,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
          singletonBudget x) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v ≤
      ∑ x ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
          v Ω true true true,
        singletonBudget x := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_singletonOptionNonemptyClassifiedSet_sum_of_boundary
      β H n Ω hv]
  exact Finset.sum_le_sum fun x hx => hpoint x hx

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_le_singletonOptionShare_sum_mul_of_boundary
    {β H R : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {singletonShare : Option (FK.boxVerts 3 n) → ℝ}
    (hpoint :
      ∀ x ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
            v Ω true true true,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ω v
            (finiteBoundaryGhostSourceClassEndpointMarkedSources
                v true true true ∪
              ({x} : Finset (Option (FK.boxVerts 3 n)))) ≤
          singletonShare x * R) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v ≤
      (∑ x ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
          v Ω true true true,
        singletonShare x) * R := by
  classical
  let liveOptions :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSingletonOptionNonemptyClassifiedSet
      v Ω true true true
  have hbudget :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
          β H n Ω v ≤
        ∑ x ∈ liveOptions, singletonShare x * R :=
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_le_singletonOptionNonemptyClassifiedSet_singletonBudget_sum_of_boundary
      (β := β) (H := H) (n := n) (Ω := Ω) (v := v) hv
      (singletonBudget := fun x => singletonShare x * R)
      (by
        intro x hx
        exact hpoint x (by simpa [liveOptions] using hx))
  calc
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v ≤
      ∑ x ∈ liveOptions, singletonShare x * R := hbudget
    _ = (∑ x ∈ liveOptions, singletonShare x) * R := by
      rw [Finset.sum_mul]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_le_supportResidualExactCardSourceClassSet_card_mul_singletonMaxCap_of_boundary
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n)) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
        β H n Ω v ≤
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
          n Ω v true true true 1).card : ℝ) *
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
          β H n Ω v hv := by
  classical
  let supportSet :=
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet
      n Ω v true true true 1
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution_eq_sourceSupport_unmarkedResidualCard_one_sum_of_boundary
      β H n Ω hv]
  change
    (∑ S ∈ supportSet,
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v S) ≤
      (supportSet.card : ℝ) *
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
          β H n Ω v hv
  have hsum :
      (∑ S ∈ supportSet,
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v S) ≤
        ∑ _S ∈ supportSet,
          finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap
            β H n Ω v hv := by
    refine Finset.sum_le_sum ?_
    intro S hS
    have hSinfo :
        S ∈
            finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
              n Ω v ∧
          finiteBoundaryGhostSourceClassEndpointMembershipCase v S =
              finiteBoundaryGhostSourceClassEndpointMembershipLabel
                SourceClassCardinalityCase.fourPlus true true true ∧
          (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S).card =
            1 := by
      exact
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSet_mem_iff.mp
          hS
    rcases Finset.card_eq_one.mp hSinfo.2.2 with ⟨x, hxresidual⟩
    have hxResidual :
        x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S := by
      simp [hxresidual]
    have hxUnmarked :
        x ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedOptions v :=
      (finiteBoundaryGhostSourceClassEndpointUnmarkedResidual_mem_iff.mp
        hxResidual).2
    have hS_eq :
        S =
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v true true true ∪
            ({x} : Finset (Option (FK.boxVerts 3 n))) := by
      have hunion :
          finiteBoundaryGhostSourceClassEndpointMarkedSources
              v true true true ∪
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidual v S =
              S :=
        finiteBoundaryGhostSourceClassEndpointMarkedSources_union_unmarkedResidual_eq_of_endpointMembershipCase_eq_label
          hSinfo.2.1
      simpa [hxresidual] using hunion.symm
    simpa [hS_eq] using
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointSingletonMaxCap_pointwise
        β H n Ω hv x hxUnmarked
  simpa [Finset.sum_const, nsmul_eq_mul, supportSet] using hsum

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointContribution_lt_of_cardOne_add_tail_lt
    {β H bound : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (h :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointCardOneContribution
          β H n Ω v +
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointTailContribution
          β H n Ω v < bound) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointContribution
        β H n Ω v < bound := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointContribution_eq_cardOne_add_tail]
  exact h

end Exact3D
end StatMech
