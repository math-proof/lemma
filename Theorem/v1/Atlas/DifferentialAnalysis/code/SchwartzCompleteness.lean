/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCompleteness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Analysis.Normed.Group.Tannery
public import Def.v1.Atlas.DifferentialAnalysis.code.SchwartzMetric
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzMetric
open scoped SchwartzMap

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]


/-- The Schwartz space `𝓢(E, F)` is complete (Melrose Prop. 6.7 / 7.4-adjacent statement),
stated as a top-level theorem so it can be reused without depending on instance synthesis. -/
theorem instCompleteSpace_axiom :
    CompleteSpace 𝓢(E, F) :=
  instCompleteSpaceSchwartz

