/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part8
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


theorem frp_bk_criterion (K : FiniteRangeKernel d) (beta : ℝ)
    (Lam S : Finset (Site d)) (u : Site d) (B : Set (Site d))
    (huS : u ∈ S) (hBS : ∀ z ∈ B, z ∉ S) :
    (frpMeasure K beta).real
        (connEvent (frpGraph K) (Lam : Set (Site d)) u B) ≤
      ∑ q ∈ frpBoundaryPairs K S,
        (frpEdgeParam K beta s(q.1, q.2) : ℝ) *
          (frpMeasure K beta).real
            (connEvent (frpGraph K) (S : Set (Site d)) u {q.1}) *
          (frpMeasure K beta).real
            (connEvent (frpGraph K) (Lam : Set (Site d)) q.2 B) := by
  classical
  let bnd := frpBoundaryPairs K S
  let P : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    connEvent (frpGraph K) (S : Set (Site d)) u {q.1}
  let Q : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    edgeOpenEvent q.1 q.2
  let R : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    connEvent (frpGraph K) (Lam : Set (Site d)) q.2 B
  let F := frpFirstExitSupport K S Lam
  have hPdep : ∀ q ∈ bnd, DependsOn (P q) (F : Set (Sym2 (Site d))) := by
    intro q _
    apply (frp_connEvent_dependsOn K S u q.1).mono
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  have hQdep : ∀ q ∈ bnd, DependsOn (Q q) (F : Set (Sym2 (Site d))) := by
    intro q hq
    apply (frp_edgeOpen_dependsOn q.1 q.2).mono
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst e
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hRdep : ∀ q ∈ bnd, DependsOn (R q) (F : Set (Sym2 (Site d))) := by
    intro q _
    apply (frp_connEvent_set_dependsOn K Lam q.2 B).mono
    intro e he
    exact Finset.mem_union_right _ he
  have hcrit := inhom_bk_criterion_of_finite_dependsOn
    (frpEdgeParam K beta) (frpEdgeParam_le_one K beta)
    bnd P Q R F hPdep hQdep hRdep
    (fun q _ => isIncreasing_connEvent (frpGraph K) (S : Set (Site d)) u {q.1})
    (fun q _ => isIncreasing_edgeOpenEvent q.1 q.2)
    (fun q _ => isIncreasing_connEvent (frpGraph K) (Lam : Set (Site d)) q.2 B)
    (frp_firstExit_inclusion K (Lam : Set (Site d)) S B u huS hBS)
  change (frpMeasure K beta).real
      (connEvent (frpGraph K) (Lam : Set (Site d)) u B) ≤ _
  calc
    (frpMeasure K beta).real
        (connEvent (frpGraph K) (Lam : Set (Site d)) u B) ≤
        ∑ q ∈ bnd, (frpMeasure K beta).real (P q) *
          (frpMeasure K beta).real (Q q) *
          (frpMeasure K beta).real (R q) := hcrit
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [show (frpMeasure K beta).real (Q q) =
          (frpEdgeParam K beta s(q.1, q.2) : ℝ) by
        exact inhom_coord_true_prob (frpEdgeParam K beta)
          (frpEdgeParam_le_one K beta) s(q.1, q.2)]
      simp only [bnd, P, R]
      ring


end Sharpness
end StatMech
