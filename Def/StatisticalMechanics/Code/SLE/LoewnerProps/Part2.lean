/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerProps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerODE
import Theorem.StatisticalMechanics.Code.SLE.LoewnerProps.Part2
open Complex Set Filter Topology
open scoped NNReal ComplexConjugate


namespace StatMech.SLE

def HasCapacityRate (g : ℝ → ℂ → ℂ) (a : ℝ) : Prop :=
  ∀ t ∈ Set.Ici (0 : ℝ), HasHalfPlaneCapacity (g t) (a * t)


end StatMech.SLE
