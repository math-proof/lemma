/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc76bsplitsink.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc75bcyclespace
import Def.StatisticalMechanics.Code.Walls.gc76bsplitsink
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
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc76b_disjointConnectors_of_splitFlow (ends : ι → Sym2 W)
    {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPsrc : sources ends P = ({o, g} : Finset W))
    (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    ∃ P', P' ⊆ K ∪ L ∧ sources ends P' = ({o, g} : Finset W) ∧ Disjoint P' D ∧ connK ends P' o g :=
  ⟨P, hPG, hPsrc, hPD, hPconn⟩


theorem gc76b_survives_of_splitFlow (ends : ι → Sym2 W)
    {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends ((K ∪ L) \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn


theorem gc76b_splitCut_card_ge2_of_flow (ends : ι → Sym2 W)
    {K L : Finset ι} {o y g : W} {P₁ P₂ : Finset ι}
    (hP₁G : P₁ ⊆ K ∪ L) (hP₁conn : connK ends P₁ o g)
    (hP₂G : P₂ ⊆ K ∪ L) (hP₂conn : connK ends P₂ y g)
    (hdisj : Disjoint P₁ P₂)
    {C : Finset ι} (hC : gc76b_IsSplitCut ends K L o y g C) :
    2 ≤ #C := by
  obtain ⟨hCG, hCo, hCy⟩ := hC
  
  have hmeet₁ : (P₁ ∩ C).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hempty
    exact hCo (mng_connK_of_disjoint ends hP₁G hempty hP₁conn)
  have hmeet₂ : (P₂ ∩ C).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hempty
    exact hCy (mng_connK_of_disjoint ends hP₂G hempty hP₂conn)
  obtain ⟨a, ha⟩ := hmeet₁
  obtain ⟨b, hb⟩ := hmeet₂
  rw [Finset.mem_inter] at ha hb
  have hab : a ≠ b := by
    intro h; subst h
    exact (Finset.disjoint_left.1 hdisj) ha.1 hb.1
  have hsub : ({a, b} : Finset ι) ⊆ C := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ha.2
    · exact hb.2
  calc (2 : ℕ) = #({a, b} : Finset ι) := by rw [Finset.card_pair hab]
    _ ≤ #C := Finset.card_le_card hsub


end Abstract
end StatMech.Walls
