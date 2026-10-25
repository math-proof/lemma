/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wisindicatorsteps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle.Part2
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Def.StatisticalMechanics.Code.Walls.wisindicatorsteps.Part5
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wis_twoToggle_nonzeroDiffs :
    wis_nonzeroDiffs wis_twoToggle 3 = [1, -1] := by
  unfold wis_nonzeroDiffs wis_twoToggle
  decide


theorem wis_twoToggle_isIndicatorStep :
    ∃ ind : ℕ → ℤ,
      (∀ e ∈ ([1, -1] : List ℤ), e = 1 ∨ e = -1) ∧ ind 0 = 0 ∧
      (∀ m, ind m = 0 ∨ ind m = 1) ∧
      ([1, -1] : List ℤ) = (List.range 2).map (fun i => ind (i + 1) - ind i) := by
  have h := wis_nonzeroDiffs_isIndicatorStep wis_twoToggle
    (fun n => by unfold wis_twoToggle; by_cases h : n = 1 ∨ n = 2 <;> simp [h]) rfl 3
  rw [wis_twoToggle_nonzeroDiffs] at h
  simpa using h


theorem wis_twoToggle_alternates : wnu_Alt ([1, -1] : List ℤ) := by
  refine ⟨Or.inl rfl, by norm_num, ?_⟩
  exact Or.inr rfl


end Lattice
end StatMech
