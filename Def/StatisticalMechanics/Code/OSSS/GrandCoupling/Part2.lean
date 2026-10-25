/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/GrandCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part4
import Theorem.StatisticalMechanics.Code.Probability.ContinuousFKG.Part3
import Theorem.StatisticalMechanics.Code.OSSS.GrandCoupling
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace GrandCoupling

open OSSS.Monotonic OSSS.Coding StatMech.Probability

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def rawInterval (μ : ConfigSpace E → ℝ) {n : ℕ} (σ : Fin n → E)
    (x : ConfigSpace E) (t : Fin n) : Set ℝ :=
  if x (σ t) then Set.Ici (thr μ σ x t) else Set.Iio (thr μ σ x t)


end GrandCoupling
end OSSS
end StatMech
