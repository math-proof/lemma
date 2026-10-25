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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part42
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

namespace FinsetFiberIndex

theorem mem_fiber {β : Type*}
    (I : FinsetFiberIndex β) (b : β) (a : I.α) :
    a ∈ I.fiber b ↔ a ∈ I.domain ∧ I.map a = b := by
  classical
  simp [fiber]


theorem mem_image {β : Type*}
    (I : FinsetFiberIndex β) (b : β) :
    b ∈ I.image ↔ ∃ a, a ∈ I.domain ∧ I.map a = b := by
  classical
  simp [image]


theorem image_card_le_domain_card {β : Type*}
    (I : FinsetFiberIndex β) :
    (I.image.card : ℝ) ≤ (I.domain.card : ℝ) := by
  classical
  have h : (I.domain.image I.map).card ≤ I.domain.card :=
    Finset.card_image_le
  exact_mod_cast (by
    simpa [image] using h)


theorem sum_fiber_weight {β : Type*}
    (I : FinsetFiberIndex β) (W : β → ℝ) :
    Finset.sum I.domain (fun a => W (I.map a)) =
      Finset.sum I.image
        (fun b => ((I.fiber b).card : ℝ) * W b) := by
  classical
  letI : DecidableEq β := Classical.decEq _
  simpa [image, fiber] using
    (finset_sum_image_fiber_card_mul I.domain I.map W)


theorem sum_le_const_mul_image_sum_of_fiber_card_le {β : Type*}
    (I : FinsetFiberIndex β) (W : β → ℝ) {B : ℝ}
    (hcard : ∀ b, b ∈ I.image → ((I.fiber b).card : ℝ) ≤ B)
    (hW : ∀ b, b ∈ I.image → 0 ≤ W b) :
    Finset.sum I.domain (fun a => W (I.map a)) ≤
      B * Finset.sum I.image W := by
  classical
  calc
    Finset.sum I.domain (fun a => W (I.map a)) =
        Finset.sum I.image
          (fun b => ((I.fiber b).card : ℝ) * W b) :=
      sum_fiber_weight I W
    _ ≤ Finset.sum I.image (fun b => B * W b) := by
      refine Finset.sum_le_sum ?_
      intro b hb
      exact mul_le_mul_of_nonneg_right (hcard b hb) (hW b hb)
    _ = B * Finset.sum I.image W := by
      rw [← Finset.mul_sum]


theorem image_sum_le_image_sum_mul_of_fiber_card_le {β : Type*}
    (I : FinsetFiberIndex β) (W C : β → ℝ)
    (hcard : ∀ b, b ∈ I.image → ((I.fiber b).card : ℝ) ≤ C b)
    (hW : ∀ b, b ∈ I.image → 0 ≤ W b) :
    Finset.sum I.image (fun b => ((I.fiber b).card : ℝ) * W b) ≤
      Finset.sum I.image (fun b => C b * W b) := by
  classical
  refine Finset.sum_le_sum ?_
  intro b hb
  exact mul_le_mul_of_nonneg_right (hcard b hb) (hW b hb)


theorem sum_le_image_sum_mul_of_fiber_card_le {β : Type*}
    (I : FinsetFiberIndex β) (W C : β → ℝ)
    (hcard : ∀ b, b ∈ I.image → ((I.fiber b).card : ℝ) ≤ C b)
    (hW : ∀ b, b ∈ I.image → 0 ≤ W b) :
    Finset.sum I.domain (fun a => W (I.map a)) ≤
      Finset.sum I.image (fun b => C b * W b) := by
  calc
    Finset.sum I.domain (fun a => W (I.map a)) =
        Finset.sum I.image
          (fun b => ((I.fiber b).card : ℝ) * W b) :=
      sum_fiber_weight I W
    _ ≤ Finset.sum I.image (fun b => C b * W b) :=
      image_sum_le_image_sum_mul_of_fiber_card_le I W C hcard hW

end FinsetFiberIndex
end Exact3D
end StatMech
