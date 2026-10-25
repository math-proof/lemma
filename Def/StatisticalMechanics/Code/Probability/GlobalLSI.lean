/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/GlobalLSI.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.EntropySubadd.Part2
import Theorem.StatisticalMechanics.Code.Probability.TwoPointLSI
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {n : ℕ}


noncomputable def gls_deriv (f : ConfigSpace (Fin n) → ℝ) (e : Fin n) (ω : ConfigSpace (Fin n)) : ℝ :=
  f (StatMech.setOpen e ω) - f (StatMech.setClosed e ω)


end StatMech.Probability
