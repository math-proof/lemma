/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc75bcyclespace
import Theorem.StatisticalMechanics.Code.Walls.gc67removable
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


theorem gc77b_ox_in_K (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K : Finset ι} {o x : W} (hox : o ≠ x) (hKsrc : sources ends K = ({o, x} : Finset W)) :
    connK ends K o x := by
  apply path_exists ends K (fun i _ => hnd i) o x
  · rw [← mem_sources, hKsrc]; simp
  · intro z hz; rw [← mem_sources, hKsrc] at hz; simpa using hz
  · exact hox


theorem gc77b_ox_survives (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o x : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W)) (hDV : D ⊆ univ \ K) :
    connK ends ((K ∪ L) \ D) o x :=
  gc68_ox_survives ends hnd hox hKsrc hDV


theorem gc77b_og_survives_of_ogInK (ends : ι → Sym2 W)
    {K L D : Finset ι} {o g : W} (hDV : D ⊆ univ \ K) (hogK : connK ends K o g) :
    connK ends ((K ∪ L) \ D) o g :=
  mng_connK_mono ends (gc68_K_survives hDV) hogK


theorem gc77b_twoCommodityLeaf_of_ogInK (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hogK : connK ends K o g) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hD1⟩ := gc67b_choose_D ends hnd K hoy hog hxy hxg hyg huniv hKsrc
  refine gc74b_twoCommodityLeaf_of_bridgeConnectors ends hnd K hog hDV hDsrc hD1 ?_
  intro L hL
  
  have hsurv : connK ends ((K ∪ L) \ D) o g := gc77b_og_survives_of_ogInK ends hDV hogK
  exact gc72_trim_to_ogBoundary ends hnd hog hsurv


theorem gc77b_ogSurvives_iff_xgSurvives (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o x g : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W)) (hDV : D ⊆ univ \ K) :
    connK ends ((K ∪ L) \ D) x g ↔ connK ends ((K ∪ L) \ D) o g :=
  gc68_xg_iff_og_survives ends hnd hox hKsrc hDV


theorem gc77b_leaf_of_xgSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hxg : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  refine gc73b_twoCommodityLeaf_of_notCut ends hnd K hog hDV hDsrc hD1 ?_
  intro L hL
  exact (gc77b_ogSurvives_iff_xgSurvives ends hnd hox hKsrc hDV).1 (hxg L hL)


theorem gc77b_twoCommodityLeaf_dichotomy (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hcov : connK ends K o g ∨
      (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1
        ∧ ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g)) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  rcases hcov with hogK | ⟨D, hDV, hDsrc, hD1, hxgsurv⟩
  · exact gc77b_twoCommodityLeaf_of_ogInK ends hnd K hoy hog hxy hxg hyg huniv hKsrc hogK
  · exact gc77b_leaf_of_xgSurvival ends hnd K hox hog hKsrc hDV hDsrc hD1 hxgsurv

end Abstract
end StatMech.Walls
