/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.FSMartingale.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.MaxElementDecomp
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]


theorem mxd_maxE_mem [Nonempty ι] {S : Finset ι} (hS : S.Nonempty) : mxd_maxE S ∈ S := by
  unfold mxd_maxE; rw [dif_pos hS]; exact S.max'_mem hS


theorem mxd_le_maxE [Nonempty ι] {S : Finset ι} {x : ι} (hx : x ∈ S) :
    x ≤ mxd_maxE S := by
  have hS : S.Nonempty := ⟨x, hx⟩
  unfold mxd_maxE; rw [dif_pos hS]; exact S.le_max' x hx


end StatMech.Probability
