/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc77bdirect.Part2
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


theorem gc78b_ox_in_K (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K : Finset ι} {o x : W} (hox : o ≠ x) (hKsrc : sources ends K = ({o, x} : Finset W)) :
    connK ends K o x :=
  gc77b_ox_in_K ends hnd hox hKsrc


theorem gc78b_xg_in_K_iff_og_in_K (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K : Finset ι} {o x g : W} (hox : o ≠ x) (hKsrc : sources ends K = ({o, x} : Finset W)) :
    connK ends K x g ↔ connK ends K o g := by
  have hoxK : connK ends K o x := gc78b_ox_in_K ends hnd hox hKsrc
  constructor
  · intro hxg; exact hoxK.trans hxg
  · intro hog; exact (connK_symm ends _ hoxK).trans hog


theorem gc78b_twoCommodityLeaf_of_xgInK (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hxgK : connK ends K x g) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  have hogK : connK ends K o g := (gc78b_xg_in_K_iff_og_in_K ends hnd hox hKsrc).1 hxgK
  exact gc77b_twoCommodityLeaf_of_ogInK ends hnd K hoy hog hxy hxg hyg huniv hKsrc hogK


theorem gc78b_xgSurvives_iff_ogSurvives (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o x g : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W)) (hDV : D ⊆ univ \ K) :
    connK ends ((K ∪ L) \ D) x g ↔ connK ends ((K ∪ L) \ D) o g :=
  gc68_xg_iff_og_survives ends hnd hox hKsrc hDV


theorem gc78b_leaf_of_xgSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hxg : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g) :
    gc71_TwoCommodityLeaf ends K o x y g :=
  gc77b_leaf_of_xgSurvival ends hnd K hox hog hKsrc hDV hDsrc hD1 hxg


theorem gc78b_twoCommodityLeaf_dichotomy (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hcov : connK ends K x g ∨
      (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1
        ∧ ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g)) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  rcases hcov with hxgK | ⟨D, hDV, hDsrc, hD1, hxgsurv⟩
  · exact gc78b_twoCommodityLeaf_of_xgInK ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc hxgK
  · exact gc78b_leaf_of_xgSurvival ends hnd K hox hog hKsrc hDV hDsrc hD1 hxgsurv

end Abstract
end StatMech.Walls
