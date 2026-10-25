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
import Structure.v1.Atlas.DifferentialAnalysis.code.PseudoDiffComposition


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
  coe_injective' f g h := by cases f; cases g; congr

end SmoothZeroAtInfty
end PoissonEquation
end
