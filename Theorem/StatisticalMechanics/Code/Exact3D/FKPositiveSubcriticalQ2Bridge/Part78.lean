module
public import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
public import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
public import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
public import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
public import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
public import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
public import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
public import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
public import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
public import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
public import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
public import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
public import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part80
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

theorem
    finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile_eq_currentProfile
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile
        β H n Ω =
      finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCurrentProfile
        β H n Ω := by
  classical
  unfold finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile
    finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCurrentProfile
  refine Finset.sum_congr rfl ?_
  intro v _hv
  rw [finiteBoundaryGhostCollapsedTwoPointDenominator_eq_currentSum_mul]


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicityCollapsedProfile
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile β H n Ω := by
  simpa [finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile] using
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_collapsedCutoffBoundaryMultiplicity_emptyCollapsedSum_sum
      (β := β) (H := H) hβ hH Ω


theorem
    finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_tanh_mul_normalizedCutoffBoundaryMultiplicityCollapsedProfile
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (hT : Real.tanh (β * H) ≠ 0) :
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
      Real.tanh (β * H) *
        finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile
          β H n Ω := by
  calc
    (∑ m ∈ Ω, finiteBoundaryGhostCollapsedSourceSummand β H n m) ≤
        finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile
          β H n Ω :=
      finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicityCollapsedProfile
        (β := β) (H := H) hβ hH Ω
    _ =
        Real.tanh (β * H) *
          finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile
            β H n Ω :=
      finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile_eq_tanh_mul_normalized
        Ω hT


end Exact3D
end StatMech
