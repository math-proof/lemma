/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg.Part3
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace Lindeberg

open OSSS.Monotonic OSSS.Coding

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def delta (μ : ConfigSpace E → ℝ) (F : Finset E) (e : E) (f : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) : ℝ :=
  cExp μ (insert e F) f (setOpen e ω) - cExp μ (insert e F) f (setClosed e ω)


end Lindeberg
end OSSS
end StatMech
