/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc79breserve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc78bxside.Part2
import Def.StatisticalMechanics.Code.Walls.gc79breserve
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


theorem gc79b_reservedGEdge_exists (ends : ι → Sym2 W) {D : Finset ι} {g : W}
    (hD1 : degK ends D g = 1) :
    ∃ eY, gc79b_gEdges ends D g = {eY} ∧ eY ∈ D ∧ g ∈ ends eY := by
  have hcard : #(gc79b_gEdges ends D g) = 1 := hD1
  rw [Finset.card_eq_one] at hcard
  obtain ⟨eY, heY⟩ := hcard
  have hmem : eY ∈ gc79b_gEdges ends D g := by rw [heY]; exact Finset.mem_singleton_self eY
  rw [gc79b_gEdges, Finset.mem_filter] at hmem
  exact ⟨eY, heY, hmem.1, hmem.2⟩


theorem gc79b_leaf_of_reservedSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hog : o ≠ g)
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hsurv : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) :
    gc71_TwoCommodityLeaf ends K o x y g :=
  gc73b_twoCommodityLeaf_of_notCut ends hnd K hog hDV hDsrc hD1 hsurv


theorem gc79b_leaf_of_reservedSurvival_xg (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hsurv : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  refine gc79b_leaf_of_reservedSurvival ends hnd K hog hDV hDsrc hD1 ?_
  intro L hL
  exact (gc78b_xgSurvives_iff_ogSurvives ends hnd hox hKsrc hDV).1 (hsurv L hL)

end Abstract
end StatMech.Walls
