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
public import Instance.v1.Atlas.DifferentialAnalysis.code.PseudoDiffComposition

@[expose] public section

noncomputable section

open scoped SchwartzMap

open Filter Topology MeasureTheory

namespace PoissonEquation

variable (n : ℕ)

namespace SmoothZeroAtInfty

variable {n}

/-- `IsLaplacianOf n f g` says that `g = -Δ f` pointwise, where `Δ` is the standard Laplacian on `ℝⁿ` defined via the iterated Fréchet derivative. -/
def IsLaplacianOf (n : ℕ) (f g : EuclideanSpace ℝ (Fin n) → ℂ) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n),
    g x = -∑ j : Fin n,
      (iteratedFDeriv ℝ 2 f x) (fun _ => EuclideanSpace.single j (1 : ℝ))


end SmoothZeroAtInfty
end PoissonEquation
end
