/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/PseudoDiffComposition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Def.v1.Atlas.DifferentialAnalysis.code.DifferentialOperators.Part2
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.DifferentialOperators
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.LaplacianExistence
import Instance.v1.Atlas.DifferentialAnalysis.code.PseudoDiffComposition


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
