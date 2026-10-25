/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace Lindeberg

open OSSS.Monotonic OSSS.Coding

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def mean (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) : ℝ :=
  ∑ ω, g ω * μ ω


noncomputable def cov (μ : ConfigSpace E → ℝ) (f g : ConfigSpace E → ℝ) : ℝ :=
  mean μ (fun ω => f ω * g ω) - mean μ f * mean μ g


noncomputable def var (μ : ConfigSpace E → ℝ) (g : ConfigSpace E → ℝ) : ℝ := cov μ g g


noncomputable def coord (e : E) : ConfigSpace E → ℝ := fun ω => if ω e then (1 : ℝ) else 0

end Lindeberg
end OSSS
end StatMech
