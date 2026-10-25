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
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def khc_sign (b : Bool) : ℝ := if b then -1 else 1

end Probability
end StatMech
