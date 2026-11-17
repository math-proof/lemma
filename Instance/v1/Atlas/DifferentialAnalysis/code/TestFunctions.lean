/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/TestFunctions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Abbrev.v1.Atlas.DifferentialAnalysis.code.TestFunctions

@[expose] public section

open scoped ZeroAtInfty
open Filter Topology


noncomputable section

namespace TestFunctions

variable (n : ℕ)

section RestrictionOfFunctionals

open ContinuousLinearMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

variable {U : Type*} [SeminormedAddCommGroup U] [NormedSpace 𝕜 U]

variable {n}

section SchwartzSpace

variable (n : ℕ)

namespace SchwartzTestFunctionSpace

variable {n : ℕ}

/-- `SchwartzTestFunctionSpace n` coerces to functions `ℝⁿ → ℂ`. -/
instance instFunLike : FunLike (SchwartzTestFunctionSpace n) (EuclideanSpace ℝ (Fin n)) ℂ where
  coe f := f.toFun
  coe_injective f g h := by cases f; cases g; congr

end SchwartzTestFunctionSpace
end SchwartzSpace
end RestrictionOfFunctionals
end TestFunctions
end
