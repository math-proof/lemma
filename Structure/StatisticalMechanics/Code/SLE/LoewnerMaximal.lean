/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

structure LoewnerForwardSolution (W : ℝ → ℝ) (z : ℂ) (T : ℝ) where
  curve : ℝ → ℂ
  initial : curve 0 = z
  deriv : ∀ t ∈ Icc (0 : ℝ) T,
    HasDerivWithinAt curve (loewnerField W t (curve t)) (Icc (0 : ℝ) T) t
  upper : ∀ t ∈ Icc (0 : ℝ) T, curve t ∈ upperHalfPlane


end StatMech.SLE
