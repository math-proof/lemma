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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part72
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem finiteBoundaryGhostCurrentOnePoint_eq_currentSumRatio
    (d n : ℕ) (β H : ℝ) :
    finiteBoundaryGhostCurrentOnePoint d n β H =
      Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph d n)) β
          (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
          (finiteBoundaryGhostOnePointSource d n) /
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph d n)) β
          (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1)) ∅ := by
  rfl


theorem finiteBoundaryGhostCurrentOnePoint_eq_expectationJ
    (d n : ℕ) (β H : ℝ) :
    finiteBoundaryGhostCurrentOnePoint d n β H =
      Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph d n)) β
        (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
        (finiteBoundaryGhostOnePointSource d n) := by
  classical
  unfold finiteBoundaryGhostCurrentOnePoint
  exact (Sharpness.current_representation
    (Sharpness.withGhost (FK.boxGraph d n)) β
    (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
    (finiteBoundaryGhostOnePointSource d n)).symm


theorem finiteBoundaryGhostCurrentOnePoint_nonneg
    (d n : ℕ) {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) :
    0 ≤ finiteBoundaryGhostCurrentOnePoint d n β H := by
  classical
  unfold finiteBoundaryGhostCurrentOnePoint
  have hJ :
      ∀ e, 0 ≤
        boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1) e :=
    boundaryGhostCoupling_nonneg (FK.boxBoundary d n) hH
      (fun _ => by norm_num)
  refine div_nonneg ?_ ?_
  · exact Sharpness.ssl_currentSum_nonneg
      (Sharpness.withGhost (FK.boxGraph d n)) β
      (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
      hβ hJ (finiteBoundaryGhostOnePointSource d n)
  · exact Sharpness.ssl_currentSum_nonneg
      (Sharpness.withGhost (FK.boxGraph d n)) β
      (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
      hβ hJ ∅


theorem finiteBoundaryGhostCurrentOnePoint_eq_expectationJ_pair
    (d n : ℕ) (β H : ℝ) :
    finiteBoundaryGhostCurrentOnePoint d n β H =
      Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph d n)) β
        (boundaryGhostCoupling (FK.boxBoundary d n) H (fun _ => 1))
        ({some (IsingFK.boxOrigin d n), none} :
          Finset (Option (FK.boxVerts d n))) := by
  simpa [finiteBoundaryGhostOnePointSource] using
    finiteBoundaryGhostCurrentOnePoint_eq_expectationJ d n β H


theorem spinProd_some_none_split
    {V : Type*} [DecidableEq V]
    (o : V) (b : Bool) (τ : ConfigSpace V) :
    Ising.spinProd ({some o, none} : Finset (Option V))
      (fun a => Option.rec b τ a) = Ising.spin τ o * Ising.spinB b := by
  unfold Ising.spinProd Ising.spinB Ising.spin
  by_cases hb : b <;> by_cases ho : τ o <;> simp [hb, ho]


theorem ghostCoupling_zero_some_none_numerator_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (o : V) :
    (∑ s : ConfigSpace (Option V),
      Ising.spinProd ({some o, none} : Finset (Option V)) s *
        Sharpness.boltzmannJ (Sharpness.withGhost G) β
          (Sharpness.FieldGhostDict.ghostCoupling (0 : ℝ) β (fun _ => 1)) s) = 0 := by
  rw [Sharpness.FieldGhostDict.sum_option_config]
  rw [Fintype.sum_bool]
  simp only [spinProd_some_none_split,
    Sharpness.FieldGhostDict.fgd_ghost_weight_eq]
  simp [Ising.spinB]


theorem expectationJ_ghostCoupling_zero_some_none_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (o : V) :
    Sharpness.expectationJ (Sharpness.withGhost G) β
      (Sharpness.FieldGhostDict.ghostCoupling (0 : ℝ) β (fun _ => 1))
      ({some o, none} : Finset (Option V)) = 0 := by
  unfold Sharpness.expectationJ
  rw [ghostCoupling_zero_some_none_numerator_eq_zero]
  simp


theorem finiteBoundaryGhostExpectation_zeroField_eq_zero
    (β : ℝ) (n : ℕ) :
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1))
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {none}) = 0 := by
  rw [boundaryGhostCoupling_zero_eq_ghostCoupling_zero
    (FK.boxBoundary 3 n) β]
  rw [← finiteBoundaryGhostOnePointSource_eq_symmDiff 3 n]
  simpa [finiteBoundaryGhostOnePointSource] using
    expectationJ_ghostCoupling_zero_some_none_eq_zero
      (FK.boxGraph 3 n) β (IsingFK.boxOrigin 3 n)


end Exact3D
end StatMech
