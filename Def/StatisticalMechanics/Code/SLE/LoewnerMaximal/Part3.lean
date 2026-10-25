/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part3
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

def LoewnerForwardSolution.timeShift
    {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (g : LoewnerForwardSolution W z T) (s : ℝ) (hs0 : 0 ≤ s) :
    LoewnerForwardSolution (fun u ↦ W (s + u)) (g.curve s) (T - s) where
  curve := fun u ↦ g.curve (s + u)
  initial := by simp
  deriv := by
    intro u hu
    have hmap : MapsTo (fun r : ℝ ↦ s + r) (Icc (0 : ℝ) (T - s)) (Icc 0 T) := by
      intro r hr
      change 0 ≤ s + r ∧ s + r ≤ T
      constructor <;> linarith [hr.1, hr.2]
    have hsu : s + u ∈ Icc (0 : ℝ) T := hmap hu
    have hinner : HasDerivWithinAt (fun r : ℝ ↦ s + r) 1
        (Icc (0 : ℝ) (T - s)) u := by
      simpa using ((hasDerivAt_const u s).add (hasDerivAt_id u)).hasDerivWithinAt
    simpa only [Function.comp_def, one_smul] using
      (g.deriv (s + u) hsu).scomp u hinner hmap
  upper := by
    intro u hu
    exact g.upper (s + u) ⟨by linarith [hu.1], by linarith [hu.2]⟩


end StatMech.SLE
