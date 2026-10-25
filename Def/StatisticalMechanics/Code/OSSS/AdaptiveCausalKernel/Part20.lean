/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveTau
import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
import Theorem.StatisticalMechanics.Code.OSSS.PredictableTreeQuery
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel.Part19
open scoped BigOperators
open MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false


namespace StatMech

namespace OSSS

namespace AdaptiveCausalKernel

open Coding Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def tripleCube (n : ℕ) : Measure (Fin n → ((ℝ × ℝ) × ℝ)) :=
  Measure.pi fun _ =>
    let ν := volume.restrict (Set.Icc (0 : ℝ) 1)
    (ν.prod ν).prod ν

noncomputable def tripleCubeEquiv (n : ℕ) :
    (Fin n → ((ℝ × ℝ) × ℝ)) ≃ᵐ
      (((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ)) :=
  (MeasurableEquiv.arrowProdEquivProdArrow (ℝ × ℝ) ℝ (Fin n)).trans
    (MeasurableEquiv.prodCongr
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
      (MeasurableEquiv.refl (Fin n → ℝ)))


end AdaptiveCausalKernel
end OSSS
end StatMech
