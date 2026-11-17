/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/TSPHelper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.TSPHelper
set_option maxHeartbeats 400000

public section

noncomputable section

open MeasureTheory Metric Set Real Filter

namespace TSPHelper

/-- The Lebesgue volume of the unit square $[0,1]^2$ is $1$. -/
lemma volume_unitSquare : (volume : Measure (EuclideanSpace ℝ (Fin 2))) unitSquare = 1 := by
  have heq : unitSquare = WithLp.ofLp ⁻¹' (Set.pi Set.univ (fun _ : Fin 2 => Icc (0:ℝ) 1)) := by
    ext p; simp only [unitSquare, mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Icc]
  rw [heq, (PiLp.volume_preserving_ofLp (ι := Fin 2)).measure_preimage
    ((MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)).nullMeasurableSet),
    volume_pi_pi]
  simp [Real.volume_Icc]

end TSPHelper
end
