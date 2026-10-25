/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DctDifferential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv.Part2
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.Percolation.DctDifferential.Part4
open MeasureTheory Function Set
open scoped NNReal
open StatMech


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem boxCrossProb_nonneg (d : ℕ) (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    0 ≤ boxCrossProb d p hp n :=
  measureReal_nonneg


theorem boxCrossProb_eq_prob (p : ℝ≥0) (hp : p ≤ 1) (n : ℕ) :
    boxCrossProb d p hp n
      = prob (p : ℝ) ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n)) := by
  unfold boxCrossProb
  exact realProb_cylinder_eq_prob (E := Sym2 (Site d)) p hp (boxCrossingEvent d n)
    (boxEdgeFinset d n) (boxCrossingEvent_dependsOn n)


theorem hasDerivAt_boxCrossProb (n : ℕ) (q : ℝ) :
    HasDerivAt (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n)))
      (∑ e : ↥(boxEdgeFinset d n),
        pivotalProb q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n)) e) q :=
  hasDerivAt_realProb_cylinder_pivotal (boxCrossingEvent d n)
    (boxCrossingEvent_isIncreasing n) (boxEdgeFinset d n) q


theorem deriv_boxCrossProb (n : ℕ) (q : ℝ) :
    deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) q
      = ∑ e : ↥(boxEdgeFinset d n),
          pivotalProb q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n)) e :=
  deriv_realProb_cylinder_pivotal (boxCrossingEvent d n)
    (boxCrossingEvent_isIncreasing n) (boxEdgeFinset d n) q


theorem differentiable_boxCrossProb (n : ℕ) :
    Differentiable ℝ
      (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) :=
  differentiable_realProb_cylinder (boxCrossingEvent d n) (boxEdgeFinset d n)


theorem deriv_boxCrossProb_nonneg (n : ℕ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ deriv (fun q => prob q ((boxEdgeFinset d n).restrict '' (boxCrossingEvent d n))) q := by
  rw [deriv_boxCrossProb]
  refine Finset.sum_nonneg (fun e _ => ?_)
  unfold pivotalProb configWeight edgeWeight
  refine Finset.sum_nonneg (fun ω _ => ?_)
  refine mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω) ?_
  refine Finset.prod_nonneg (fun j _ => ?_)
  by_cases h : ω j
  · simpa [h] using hq0
  · simpa [h] using sub_nonneg.mpr hq1

end Percolation
end StatMech
