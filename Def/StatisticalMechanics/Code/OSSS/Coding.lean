/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Coding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Monotonic.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.OSSS.Part6
open scoped BigOperators
open Finset MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace OSSS.Coding

open OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def condProbBit (μ : ConfigSpace E → ℝ) (F : Finset E)
    (η : ConfigSpace E) (e : E) (b : Bool) : ℝ :=
  (∑ ω, if (Agree F η ω ∧ ω e = b) then μ ω else 0) / condNorm μ F η


noncomputable def condProbClosed (μ : ConfigSpace E → ℝ) (F : Finset E)
    (η : ConfigSpace E) (e : E) : ℝ :=
  condProbBit μ F η e false


end OSSS.Coding
end StatMech
