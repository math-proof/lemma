/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/MonotonicOSSS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.RussoDerivative.Part5
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part2
open scoped BigOperators
open Finset MeasureTheory Set

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace MonotonicMeasure

variable {E : Type*} [Fintype E] [DecidableEq E]


def MonotonicOSSSBound (μ : ConfigSpace E → ℝ) (s : Finset E)
    (f : ConfigSpace E → ℝ) (N : ℕ) (c₀ D : ℝ) : Prop :=
  (N : ℝ) * c₀ * genVar μ f ≤ D * ∑ e ∈ s, genCov μ (genCoord e) f

end MonotonicMeasure
end OSSS
end StatMech
