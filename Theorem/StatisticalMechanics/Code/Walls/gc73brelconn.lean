/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc73brelconn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc72twogedge.Part2
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


theorem gc73b_perLClause_of_notCut (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o g : W} (hog : o ≠ g)
    (hsurv : connK ends ((K ∪ L) \ D) o g) :
    ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g :=
  gc72_trim_to_ogBoundary ends hnd hog hsurv


theorem gc73b_notCut_of_perLClause (ends : ι → Sym2 W)
    {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends ((K ∪ L) \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn


theorem gc73b_twoCommodityLeaf_of_notCut (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hog : o ≠ g)
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hnotcut : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  refine ⟨D, hDV, hDsrc, hD1, ?_⟩
  intro L hL
  exact gc73b_perLClause_of_notCut ends hnd hog (hnotcut L hL)


theorem gc73b_notCut_of_relConn (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L : Finset ι} {o g : W} (hog : o ≠ g)
    (hconn : connK ends (K ∪ L) o g)
    (hrel : ∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) →
        connK ends ((K ∪ L) \ P₁) o g)
    {D : Finset ι}
    (hDsub : ∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁) :
    connK ends ((K ∪ L) \ D) o g := by
  obtain ⟨P, hPG, hPsrc, hPD, hPconn⟩ :=
    gc72_ogSurvives_of_relConn ends hnd hog hconn hrel hDsub
  exact mng_connK_of_disjoint ends hPG hPD hPconn


theorem gc73b_twoCommodityLeaf_of_relConn_perL (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hrel : ∀ L ∈ gc51_LblockSet ends K o x g,
        (∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) →
            connK ends ((K ∪ L) \ P₁) o g)
          ∧ (∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁)) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  refine gc73b_twoCommodityLeaf_of_notCut ends hnd K hog hDV hDsrc hD1 ?_
  intro L hL
  obtain ⟨hrelL, hDsubL⟩ := hrel L hL
  have hconn : connK ends (K ∪ L) o g := gc72_og_in_KL ends hnd K hox hKsrc hL
  exact gc73b_notCut_of_relConn ends hnd hog hconn hrelL hDsubL


theorem gc73b_gcopyRemoval_of_fullRemoval (ends : ι → Sym2 W) {K L D : Finset ι} {eD : ι} {o g : W}
    (heD : eD ∈ D) (hsurv : connK ends ((K ∪ L) \ D) o g) :
    connK ends ((K ∪ L) \ ({eD} : Finset ι)) o g := by
  apply mng_connK_mono ends _ hsurv
  intro i hi
  rw [Finset.mem_sdiff] at hi ⊢
  refine ⟨hi.1, ?_⟩
  simp only [Finset.mem_singleton]
  intro h; subst h; exact hi.2 heD

end Abstract
end StatMech.Walls
