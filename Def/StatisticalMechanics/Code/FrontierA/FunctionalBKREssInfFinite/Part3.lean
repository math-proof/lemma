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
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKREssInfFinite.Part2
open MeasureTheory
open scoped BigOperators ENNReal NNReal


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def functionalDisjointEssMaxAt
    (p : E → NNReal) (hp : ∀ e, p e ≤ 1)
    (f g : ConfigSpace E → ℝ) (omega eta : ConfigSpace E) : ℝ :=
  (disjointCoordinatePairs E).sup' (disjointCoordinatePairs_nonempty (E := E))
    fun pair => cylinderEssInf p hp f pair.1 omega *
      cylinderEssInf p hp g pair.2 eta


noncomputable def functionalDisjointEssMax
    (p : E → NNReal) (hp : ∀ e, p e ≤ 1)
    (f g : ConfigSpace E → ℝ) (omega : ConfigSpace E) : ℝ :=
  functionalDisjointEssMaxAt p hp f g omega omega

end StatMech.FrontierA
