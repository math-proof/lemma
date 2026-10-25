/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part74
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostApprox_pointwise_of_hardFieldLimit
    {β : ℝ} {n : ℕ}
    (hlim :
      Tendsto (fun H : ℝ => finiteBoundaryGhostCurrentOnePoint 3 n β H)
        atTop
        (𝓝
          (IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
            (IsingFK.boxOrigin 3 n)))) :
    ∀ ε : ℝ, 0 < ε →
      ∃ H : ℝ, 0 ≤ H ∧
        IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
            (IsingFK.boxOrigin 3 n)
          ≤ finiteBoundaryGhostCurrentOnePoint 3 n β H + ε := by
  intro ε hε
  let target :=
    IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
      (IsingFK.boxOrigin 3 n)
  have hevent :
      ∀ᶠ H in atTop,
        dist (finiteBoundaryGhostCurrentOnePoint 3 n β H) target < ε :=
    (Metric.tendsto_nhds.mp hlim) ε hε
  have hcombined :
      ∀ᶠ H in atTop,
        0 ≤ H ∧
          dist (finiteBoundaryGhostCurrentOnePoint 3 n β H) target < ε := by
    filter_upwards [eventually_ge_atTop (0 : ℝ), hevent] with H hH hclose
    exact ⟨hH, hclose⟩
  obtain ⟨H₀, hH₀⟩ := (eventually_atTop.1 hcombined)
  let H : ℝ := max H₀ 0
  have hpair :
      0 ≤ H ∧
        dist (finiteBoundaryGhostCurrentOnePoint 3 n β H) target < ε :=
    hH₀ H (le_max_left H₀ 0)
  obtain ⟨hH_nonneg, hclose⟩ := hpair
  refine ⟨H, hH_nonneg, ?_⟩
  have habs :
      |finiteBoundaryGhostCurrentOnePoint 3 n β H - target| < ε := by
    simpa [Real.dist_eq] using hclose
  have hleft := (abs_lt.mp habs).1
  linarith


theorem finiteBoundaryGhostApprox_of_hardFieldLimit
    (hlim :
      FiniteQ2SimonBoundaryGhostHardFieldLimitPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hlim β hβpos hβc] with n hlim_n
  exact finiteBoundaryGhostApprox_pointwise_of_hardFieldLimit hlim_n


end Exact3D
end StatMech
