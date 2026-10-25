/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part3
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem exists_loewnerBackwardSegment
    {W : ℝ → ℝ} (hW : Continuous W) {s u : ℝ} (hu : 0 ≤ u)
    {y : ℂ} (hy : 0 < y.im) (hshort : u < y.im ^ 2 / 16) :
    ∃ x : ℂ, ∃ g : LoewnerForwardSolution (fun r ↦ W (s + r)) x u,
      g.curve u = y := by
  obtain ⟨α, hα, C, hC⟩ := loewner_local_flow_chart hW hy (s + u)
  have hyball : y ∈ closedBall y (y.im / 4) :=
    mem_closedBall_self (by positivity)
  obtain ⟨hendpoint, hderiv, hstrip⟩ := hα y hyball
  have hmap : MapsTo (fun r : ℝ ↦ s + r) (Icc (0 : ℝ) u)
      (Icc (s + u - y.im ^ 2 / 16) (s + u + y.im ^ 2 / 16)) := by
    intro r hr
    constructor <;> linarith [hr.1, hr.2]
  let x : ℂ := α y s
  let g : LoewnerForwardSolution (fun r ↦ W (s + r)) x u :=
    { curve := fun r ↦ α y (s + r)
      initial := by simp [x]
      deriv := by
        intro r hr
        have hinner : HasDerivWithinAt (fun q : ℝ ↦ s + q) 1
            (Icc (0 : ℝ) u) r := by
          simpa using ((hasDerivAt_const r s).add (hasDerivAt_id r)).hasDerivWithinAt
        have hd := (hderiv (s + r) (hmap hr)).scomp r hinner hmap
        simpa only [Function.comp_def, one_smul] using hd
      upper := by
        intro r hr
        exact loewnerStrip_subset_upperHalfPlane (by positivity) (hstrip (s + r)) }
  refine ⟨x, g, ?_⟩
  simpa [g] using hendpoint


end StatMech.SLE
