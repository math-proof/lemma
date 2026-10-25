/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/OSSS.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Def.StatisticalMechanics.Code.Inequalities.OSSS.Part3
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace OSSS

variable {E : Type*} [Fintype E] [DecidableEq E]


omit [Fintype E] in

lemma condMean_setOpen (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    condMean ν e g (setOpen e ω) = condMean ν e g ω := by
  unfold condMean
  rw [setOpen_setOpen, setClosed_setOpen]

omit [Fintype E] in

lemma condMean_setClosed (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    condMean ν e g (setClosed e ω) = condMean ν e g ω := by
  unfold condMean
  rw [setOpen_setClosed, setClosed_setClosed]

omit [Fintype E] in

lemma condMean_eq (ν : E → Bool → ℝ) (e : E) (g : ConfigSpace E → ℝ)
    (ω : ConfigSpace E) :
    condMean ν e g ω = ν e true * g (setOpen e ω) + ν e false * g (setClosed e ω) := rfl


end OSSS
end StatMech
