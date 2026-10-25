/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc69mengerclose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc68removalsurvival.Part2
import Theorem.StatisticalMechanics.Code.Walls.menger_general.Part7
import Theorem.StatisticalMechanics.Code.Walls.gc63reroute.Part2
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


theorem gc69b_ogReroute_of_disjointConnector (ends : ι → Sym2 W) {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends ((K ∪ L) \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn


theorem gc69b_disjointConnector_of_ogReroute (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {K L D : Finset ι} {o g : W}
    (hog : o ≠ g) (hsurv : connK ends ((K ∪ L) \ D) o g) :
    ∃ P, P ⊆ K ∪ L ∧ Disjoint P D ∧ sources ends P = ({o, g} : Finset W) ∧ connK ends P o g := by
  obtain ⟨P, hPsub, hPsrc⟩ := exists_conn_set ends ((K ∪ L) \ D) hsurv hog
  have hPG : P ⊆ K ∪ L := fun i hi => (Finset.mem_sdiff.1 (hPsub hi)).1
  have hPD : Disjoint P D := by
    rw [Finset.disjoint_left]
    intro i hi
    exact (Finset.mem_sdiff.1 (hPsub hi)).2
  refine ⟨P, hPG, hPD, hPsrc, mng_connK_of_sources ends hnd P hog hPsrc⟩


theorem gc69b_not_isCut_of_disjointConnector (ends : ι → Sym2 W) {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    ¬ mngg_IsCut ends (K ∪ L) o g D := by
  intro hC
  obtain ⟨i, hi⟩ := mngg_cut_meets_connector ends hC hPG hPconn
  rw [Finset.mem_inter] at hi
  exact (Finset.disjoint_left.1 hPD) hi.1 hi.2


end Abstract
end StatMech.Walls
