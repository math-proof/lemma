/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Lindeberg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.Coding.Part6
import Theorem.StatisticalMechanics.Code.OSSS.MonotonicOSSS.Part3
import Theorem.StatisticalMechanics.Code.OSSS.Lindeberg
open scoped BigOperators
open Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace Lindeberg

open OSSS.Monotonic OSSS.Coding

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def cExp (μ : ConfigSpace E → ℝ) (F : Finset E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) : ℝ :=
  ∑ ω', g ω' * condMass μ F ω ω'


def Fmeas (F : Finset E) (h : ConfigSpace E → ℝ) : Prop :=
  ∀ η η', (∀ f ∈ F, η f = η' f) → h η = h η'


end Lindeberg
end OSSS
end StatMech
