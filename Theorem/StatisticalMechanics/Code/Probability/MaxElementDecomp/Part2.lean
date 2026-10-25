/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MaxElementDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.FSMartingale.Part2
import Theorem.StatisticalMechanics.Code.Probability.RhoOptimiseClose2
import Def.StatisticalMechanics.Code.Probability.MaxElementDecomp.Part2
open scoped BigOperators
open Finset
open Real

set_option linter.style.longLine false


namespace StatMech.Probability

open StatMech StatMech.OSSS

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]


theorem mxd_mem_of_mem_fiber [Nonempty ι] {e : ι} {S : Finset ι} (hS : S ∈ mxd_fiber e) :
    e ∈ S := by
  unfold mxd_fiber at hS
  rw [Finset.mem_filter, Finset.mem_erase] at hS
  obtain ⟨⟨hne, _⟩, hmax⟩ := hS
  have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  rw [← hmax]; exact mxd_maxE_mem hSne


theorem mxd_fiber_subset_mem [Nonempty ι] (e : ι) :
    mxd_fiber e ⊆ univ.filter (fun S : Finset ι => e ∈ S) := by
  intro S hS
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ S, mxd_mem_of_mem_fiber hS⟩


end StatMech.Probability
