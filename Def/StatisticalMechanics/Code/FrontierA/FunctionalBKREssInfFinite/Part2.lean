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
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKREssInfFinite
open MeasureTheory
open scoped BigOperators ENNReal NNReal


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def cylinderEssInf
    (p : E → NNReal) (hp : ∀ e, p e ≤ 1)
    (f : ConfigSpace E → ℝ) (K : Set E) (omega : ConfigSpace E) : ℝ :=
  essInf (fun eta : AgreementFiberPoint K omega => f eta.1)
    (agreementFiberMeasure p hp K omega)


end StatMech.FrontierA
