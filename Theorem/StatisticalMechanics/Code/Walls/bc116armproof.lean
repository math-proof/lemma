/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc116armproof.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc114haschild.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc101mengergap
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*}

variable {G : SimpleGraph V}


theorem bc116_isInternal_of_mem_support_free (F : SimpleGraph V) {s t : V} (p : F.Walk s t)
    (hp : p.IsPath) {v : V} (hv : v ∈ p.support) (hvs : v ≠ s) (hvt : v ≠ t) :
    bc114_IsInternal F v := by
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hv
  obtain ⟨i, hvi, hile⟩ := hv
  refine ⟨s, t, p, i, hp, ?_, ?_, hvi⟩
  · rcases Nat.eq_zero_or_pos i with h0 | hpos
    · exfalso; apply hvs; rw [← hvi, h0, p.getVert_zero]
    · exact hpos
  · rcases Nat.lt_or_ge i p.length with hlt | hge
    · exact hlt
    · exfalso; apply hvt
      have : i = p.length := by omega
      rw [← hvi, this, p.getVert_length]


theorem bc116_isInternal_of_throughPath (F : SimpleGraph V) {s t : V} (p : F.Walk s t)
    (hp : p.IsPath) {v : V} (hv : v ∈ p.support) (hvs : v ≠ s) (hvt : v ≠ t) :
    bc114_IsInternal F v :=
  bc116_isInternal_of_mem_support_free F p hp hv hvs hvt


end StatMech.Walls
