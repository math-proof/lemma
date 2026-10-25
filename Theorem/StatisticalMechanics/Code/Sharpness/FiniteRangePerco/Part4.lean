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
import Instance.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part2
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


theorem frpEdgeCoupling_smul (K : FiniteRangeKernel d)
    (g : Multiplicative (Site d)) (e : Sym2 (Site d)) :
    frpEdgeCoupling K (g • e) = frpEdgeCoupling K e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [smul_sym2_mk, frpEdgeCoupling_mk, frpEdgeCoupling_mk]
      congr 1
      funext i
      rw [Pi.sub_apply]
      simp only [smul_site_apply]
      simp only [Pi.sub_apply]
      abel


theorem frpEdgeParam_smul (K : FiniteRangeKernel d) (beta : ℝ)
    (g : Multiplicative (Site d)) (e : Sym2 (Site d)) :
    frpEdgeParam K beta (g • e) = frpEdgeParam K beta e := by
  unfold frpEdgeParam
  rw [frpEdgeCoupling_smul]


theorem frpMeasure_translationInvariant (K : FiniteRangeKernel d) (beta : ℝ) :
    IsTranslationInvariant (G := Multiplicative (Site d)) (frpMeasure K beta) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  rw [shift_eq_piCongrLeft]
  let e := MulAction.toPerm (β := Sym2 (Site d)) g
  have h := Measure.infinitePi_map_piCongrLeft
    (μ := fun i : Sym2 (Site d) =>
      bernoulliMeasure (frpEdgeParam K beta i) (frpEdgeParam_le_one K beta i)) e
  change Measure.map
      (Equiv.piCongrLeft (fun _ : Sym2 (Site d) => Bool) e)
        (Measure.infinitePi (fun i =>
          bernoulliMeasure (frpEdgeParam K beta i) (frpEdgeParam_le_one K beta i))) = _
  rw [show (fun i =>
      bernoulliMeasure (frpEdgeParam K beta i) (frpEdgeParam_le_one K beta i)) =
      (fun i => bernoulliMeasure (frpEdgeParam K beta (e i))
        (frpEdgeParam_le_one K beta (e i))) from by
        funext i
        have hpi : frpEdgeParam K beta (e i) = frpEdgeParam K beta i := by
          simpa [e] using frpEdgeParam_smul K beta g i
        exact bernoulliMeasure_congr _ _ hpi.symm]
  exact h


theorem frpGraph_adj_displacement (K : FiniteRangeKernel d) {x y : Site d}
    (hxy : (frpGraph K).Adj x y) : y - x ∈ box d K.range :=
  K.support (y - x) (ne_of_gt hxy)


end Sharpness
end StatMech
