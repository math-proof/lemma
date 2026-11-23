/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffComposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Calculus.MeanValue
public import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.LaplacianExistence
public import Structure.v1.Atlas.DifferentialAnalysis.code.PseudoDiffComposition
@[expose] public section

noncomputable section

open scoped SchwartzMap

open Filter Topology MeasureTheory

namespace PoissonEquation

variable (n : ℕ)

namespace SmoothZeroAtInfty

variable {n}

/-- Treat `SmoothZeroAtInfty n` as a `FunLike` so that an element can be applied like a function. -/
instance : FunLike (SmoothZeroAtInfty n) (EuclideanSpace ℝ (Fin n)) ℂ where
  coe := SmoothZeroAtInfty.toFun
  coe_injective f g h := by cases f; cases g; congr

end SmoothZeroAtInfty
end PoissonEquation
end
