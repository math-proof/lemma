module
public import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
public import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part5
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.SLE

def IsLoewnerAdmissibleDuration (W : ℝ → ℝ) (z : ℂ) (T : ℝ) : Prop :=
  0 < T ∧ Nonempty (LoewnerForwardSolution W z T)


end StatMech.SLE
