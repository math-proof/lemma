/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/BonamiTensorize.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Logic.Equiv.Fin.Basic
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


noncomputable def bnt_uexp (f : (ι → Bool) → ℝ) : ℝ :=
  (∑ ω : ι → Bool, f ω) / (2 ^ (Fintype.card ι))


noncomputable def bnt_qnormPow (q : ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  bnt_uexp (fun ω => |f ω| ^ q)


noncomputable def bnt_qnorm (q : ℝ) (f : (ι → Bool) → ℝ) : ℝ :=
  (bnt_qnormPow q f) ^ (1 / q)


end Probability
end StatMech
