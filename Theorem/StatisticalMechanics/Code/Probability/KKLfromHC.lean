/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.VectorTwoPoint
import Theorem.StatisticalMechanics.Code.Probability.KKLInequality.Part4
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Def.StatisticalMechanics.Code.Probability.KKLfromHC
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


@[simp] theorem khc_sign_false : khc_sign false = 1 := rfl

@[simp] theorem khc_sign_true : khc_sign true = -1 := rfl


theorem khc_sign_sq (b : Bool) : khc_sign b * khc_sign b = 1 := by
  cases b <;> simp [khc_sign]


end Probability
end StatMech
