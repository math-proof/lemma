/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/CylinderDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Russo
import Theorem.StatisticalMechanics.Code.Foundations.CylinderDeriv
open MeasureTheory ProbabilityTheory Function
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*} [Countable E] [DecidableEq E]


noncomputable def extendOff (F : Finset E) (ω : ConfigSpace E) (η : ConfigSpace ↥F) :
    ConfigSpace E := fun j => if h : j ∈ F then η ⟨j, h⟩ else ω j

end StatMech
