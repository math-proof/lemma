/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc74bbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc73brelconn.Part2
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


theorem gc74b_bridgeEdge_notMem_of_survives (ends : ι → Sym2 W) {K L D : Finset ι} {eStar : ι} {o g : W}
    (hbridge : ¬ connK ends ((K ∪ L) \ ({eStar} : Finset ι)) o g)
    (hsurv : connK ends ((K ∪ L) \ D) o g) :
    eStar ∉ D := by
  intro hmem
  apply hbridge
  apply mng_connK_mono ends _ hsurv
  intro i hi
  rw [Finset.mem_sdiff] at hi ⊢
  refine ⟨hi.1, ?_⟩
  simp only [Finset.mem_singleton]
  intro h; subst h; exact hi.2 hmem


theorem gc74b_survival_of_bridge_reroute (ends : ι → Sym2 W)
    {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends ((K ∪ L) \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn


theorem gc74b_bridge_perLClause_iff (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o g : W} (hog : o ≠ g) :
    (∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g)
      ↔ connK ends ((K ∪ L) \ D) o g :=
  gc72_leafClause_iff_survives ends hnd hog


theorem gc74b_twoCommodityLeaf_of_bridgeConnectors (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W} (hog : o ≠ g)
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hconn : ∀ L ∈ gc51_LblockSet ends K o x g,
        ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  refine gc73b_twoCommodityLeaf_of_notCut ends hnd K hog hDV hDsrc hD1 ?_
  intro L hL
  obtain ⟨P, hPG, _, hPD, hPconn⟩ := hconn L hL
  exact mng_connK_of_disjoint ends hPG hPD hPconn


theorem gc74b_survives_of_gEdge_off_route (ends : ι → Sym2 W)
    {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends ((K ∪ L) \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn


theorem gc74b_bridge_survives_of_disjointConnector (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {K L D P : Finset ι} {o g : W} (hog : o ≠ g)
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    ∃ P', P' ⊆ K ∪ L ∧ sources ends P' = ({o, g} : Finset W) ∧ Disjoint P' D ∧ connK ends P' o g :=
  gc72_trim_to_ogBoundary ends hnd hog (mng_connK_of_disjoint ends hPG hPD hPconn)

end Abstract
end StatMech.Walls
