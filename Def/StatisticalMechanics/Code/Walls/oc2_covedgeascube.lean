/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/oc2_covedgeascube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling.Part3
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace Walls

open StatMech.OSSS

open StatMech.OSSS.Coding

open StatMech.OSSS.GrandCoupling

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def oc2_cubeCov (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (F G : ConfigSpace E → ℝ) : ℝ :=
  (∫ u, F (codeMap μ σ u) * G (codeMap μ σ u) ∂(Vcube n))
    - (∫ u, F (codeMap μ σ u) ∂(Vcube n)) * (∫ u, G (codeMap μ σ u) ∂(Vcube n))


end Walls
end StatMech
