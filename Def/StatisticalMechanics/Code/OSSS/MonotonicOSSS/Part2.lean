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
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS
open scoped BigOperators
open Finset MeasureTheory Set

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace MonotonicMeasure

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def genMean (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, g ω * μ ω


noncomputable def genCov (μ : ConfigSpace E → ℝ) (f g : ConfigSpace E → ℝ) : ℝ :=
  genMean μ (fun ω => f ω * g ω) - genMean μ f * genMean μ g


noncomputable def genVar (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  genCov μ g g


noncomputable def genCoord (e : E) : ConfigSpace E → ℝ := fun ω => if ω e then (1 : ℝ) else 0

end MonotonicMeasure
end OSSS
end StatMech
