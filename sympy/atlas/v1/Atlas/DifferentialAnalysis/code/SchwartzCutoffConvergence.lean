/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCutoffConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Topology.Order.Basic
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

open Filter Topology Metric
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [HasContDiffBump E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

namespace SchwartzMap

/-- A sequence of smooth bump functions `χ_m` on `E`, supported in
`B(0, m + 2)` and equal to one on `B(0, m + 1)`. -/
noncomputable def bumpSeq (m : ℕ) : ContDiffBump (0 : E) :=
  ⟨↑m + 1, ↑m + 2, by positivity, by linarith⟩

/-- Cutoff of a Schwartz function by `bumpSeq m`: multiplies `f` pointwise by the bump. -/
noncomputable def bumpCutoffMul (m : ℕ) (f : SchwartzMap E F) : SchwartzMap E F :=
  SchwartzMap.smulLeftCLM (𝕜 := ℝ) F (fun x => bumpSeq (E := E) m x) f
