/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Def.StatisticalMechanics.Code.SLE.LoewnerMaximal
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

theorem LoewnerForwardSolution.continuousOn {W : ℝ → ℝ} {z : ℂ} {T : ℝ}
    (g : LoewnerForwardSolution W z T) : ContinuousOn g.curve (Icc (0 : ℝ) T) :=
  fun t ht ↦ (g.deriv t ht).continuousWithinAt


end StatMech.SLE
