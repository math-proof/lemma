/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKREssInfFinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralDual.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralFinite
import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Mathlib.MeasureTheory.Function.EssSup
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKREssInfFinite.Part3
open MeasureTheory
open scoped BigOperators ENNReal NNReal


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def bernoulliProductWeight
    (p : E → ℝ≥0) (hp : ∀ e, p e ≤ 1) : E → Bool → ℝ :=
  fun e b => (bernoulliMeasure (p e) (hp e)).real {b}

end StatMech.FrontierA
