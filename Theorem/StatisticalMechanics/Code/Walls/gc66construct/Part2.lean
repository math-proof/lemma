/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc66construct.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc65cyclespace.Part2
import Def.StatisticalMechanics.Code.Walls.gc66construct
open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc66_choose_D (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι)
    {o x y g : W} (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hrem : gc66_RemovableGEdge ends K y g) :
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1 := by
  obtain ⟨D, hDV, hDsrc, hDmin⟩ :=
    gc63b_minConnector ends hnd K hoy hog hxy hxg hyg huniv hKsrc
  refine ⟨D, hDV, hDsrc, ?_⟩
  have hodd : Odd (degK ends D g) := gc65_ygConnector_gDeg_odd ends hDsrc
  have hge1 : 1 ≤ degK ends D g := hodd.pos
  
  by_contra hne
  have hge2 : 2 ≤ degK ends D g := by omega
  obtain ⟨i₀, hi₀D, hi₀g, hi₀conn⟩ := hrem D hDV hDsrc hge2
  obtain ⟨D', hD'D, hD'src, hlt⟩ := gc66_strictly_smaller_of_removable ends hyg hi₀D hi₀conn
  have hD'V : D' ⊆ univ \ K := hD'D.trans hDV
  exact absurd (hDmin D' hD'V hD'src) (by omega)


theorem gc66_choose_D_of_ygEdge (ends : ι → Sym2 W) {K : Finset ι} {y g : W} (hyg : y ≠ g)
    {i : ι} (hiV : i ∈ univ \ K) (hi : ends i = s(y, g)) :
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1 := by
  refine ⟨{i}, Finset.singleton_subset_iff.2 hiV, ?_, ?_⟩
  · ext z
    simp only [mem_sources, degK, Finset.filter_singleton, hi, Sym2.mem_iff, Finset.mem_insert,
      Finset.mem_singleton]
    by_cases hz : z = y ∨ z = g
    · rw [if_pos hz, Finset.card_singleton]
      constructor
      · intro _; tauto
      · intro _; exact ⟨0, rfl⟩
    · rw [if_neg hz, Finset.card_empty]
      constructor
      · intro hodd; exact absurd hodd (by decide)
      · intro h; exact absurd h hz
  · rw [degK, Finset.filter_singleton, hi]
    simp only [Sym2.mem_iff, or_true, if_true, Finset.card_singleton]


end Abstract
end StatMech.Walls
