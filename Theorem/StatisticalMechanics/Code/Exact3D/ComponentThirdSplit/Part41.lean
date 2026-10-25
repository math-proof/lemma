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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part43
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet_mem_iff
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))}
    {ι : Type*} [DecidableEq ι]
    {label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι}
    {i : ι}
    {E : finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v} :
    E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ω hasGhost hasOrigin hasEndpoint R label i ↔
      E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω hasGhost hasOrigin hasEndpoint R ∧
        label E = i := by
  simp [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet_card_le_classifiedSet_card
    {n : ℕ} (v : FK.boxVerts 3 n)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (R : Finset (Option (FK.boxVerts 3 n)))
    {ι : Type*} [DecidableEq ι]
    (label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι)
    (i : ι) :
    ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
        v Ω hasGhost hasOrigin hasEndpoint R label i).card : ℝ) ≤
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
        v Ω hasGhost hasOrigin hasEndpoint R).card : ℝ) := by
  exact_mod_cast
    Finset.card_filter_le
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
        v Ω hasGhost hasOrigin hasEndpoint R)
      (fun E => label E = i)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet_card_sum_eq_classifiedSet_card
    {n : ℕ} (v : FK.boxVerts 3 n)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (R : Finset (Option (FK.boxVerts 3 n)))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι) :
    (∑ i : ι,
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
        v Ω hasGhost hasOrigin hasEndpoint R label i).card) =
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
        v Ω hasGhost hasOrigin hasEndpoint R).card := by
  classical
  simpa [
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet]
    using
      (Finset.card_eq_sum_card_fiberwise
        (s :=
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω hasGhost hasOrigin hasEndpoint R)
        (t := (Finset.univ : Finset ι)) (f := label)
        (fun E _hE => Finset.mem_univ (label E))).symm

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum_eq_sum_labelSet
    {n : ℕ} (v : FK.boxVerts 3 n)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hasGhost hasOrigin hasEndpoint : Bool)
    (R : Finset (Option (FK.boxVerts 3 n)))
    {ι : Type*} [DecidableEq ι]
    (label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι)
    (i : ι) :
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum
        v β H Ω hasGhost hasOrigin hasEndpoint R label i =
      ∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ω hasGhost hasOrigin hasEndpoint R label i,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E := by
  rfl

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_sum_classifiedSet
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool)
    (R : Finset (Option (FK.boxVerts 3 n))) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R) =
      ∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E := by
  rfl

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_label_sum
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hasGhost hasOrigin hasEndpoint : Bool)
    (R : Finset (Option (FK.boxVerts 3 n)))
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R) =
      ∑ i : ι,
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum
          v β H Ω hasGhost hasOrigin hasEndpoint R label i := by
  classical
  unfold
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
    finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum
  rw [← Finset.sum_fiberwise_of_maps_to
    (s :=
      (finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSupport
        n Ω v).filter
        (fun E =>
          E.1 =
            finiteBoundaryGhostSourceClassEndpointMarkedSources
              v hasGhost hasOrigin hasEndpoint ∪ R))
    (t := (Finset.univ : Finset ι)) (g := label)
    (fun E _hE => Finset.mem_univ (label E))
    (fun E => finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E)]

end Exact3D
end StatMech
