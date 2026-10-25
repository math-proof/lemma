/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part2
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

def LoewnerForwardSolution.reflect {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (g : LoewnerForwardSolution W z T) :
    LoewnerForwardSolution (fun t ↦ -W t) (loewnerReflection z) T where
  curve := fun t ↦ loewnerReflection (g.curve t)
  initial := by simp [g.initial]
  deriv := by
    intro t ht
    have hconj : HasDerivWithinAt (fun s ↦ conj (g.curve s))
        (conj (loewnerField W t (g.curve t))) (Icc (0 : ℝ) T) t := by
      simpa only [Complex.conjCLE_apply] using
        Complex.conjCLE.hasFDerivAt.comp_hasDerivWithinAt t (g.deriv t ht)
    have hreflect : HasDerivWithinAt
        (fun s ↦ loewnerReflection (g.curve s))
        (loewnerReflection (loewnerField W t (g.curve t))) (Icc (0 : ℝ) T) t := by
      simpa only [loewnerReflection, Pi.neg_apply] using hconj.neg
    simpa only [loewnerReflection_loewnerField] using hreflect
  upper := by
    intro t ht
    rw [mem_upperHalfPlane]
    simpa only [loewnerReflection_im] using
      mem_upperHalfPlane.mp (g.upper t ht)


end StatMech.SLE
