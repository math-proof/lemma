/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc50threereplica.Part3
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
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  switching_card₂ connK_symm exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc51_connK_mono (ends : ι → Sym2 W) {K₁ K₂ : Finset ι} (h : K₁ ⊆ K₂) {a b : W}
    (hab : connK ends K₁ a b) : connK ends K₂ a b := by
  refine Relation.ReflTransGen.mono ?_ _ _ hab
  rintro p q ⟨i, hi, hp, hq, hpq⟩
  exact ⟨i, h hi, hp, hq, hpq⟩


theorem gc51_connK_of_sources (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (P : Finset ι) {y g : W} (hyg : y ≠ g) (hPsrc : sources ends P = ({y, g} : Finset W)) :
    connK ends P y g := by
  apply path_exists ends P (fun i _ => hnd i) y g
  · rw [← mem_sources, hPsrc]; simp
  · intro z hz; rw [← mem_sources, hPsrc] at hz; simpa using hz
  · exact hyg


theorem gc51_sdiff_sources (ends : ι → Sym2 W) {V L : Finset ι} (hLV : L ⊆ V) {y g : W}
    (hVsrc : sources ends V = ({y, g} : Finset W)) (hLsrc : sources ends L = (∅ : Finset W)) :
    sources ends (V \ L) = ({y, g} : Finset W) := by
  have hcompl : V \ L = V ∆ L := (symmDiff_of_ge hLV).symm
  rw [hcompl, sources_symmDiff, hVsrc, hLsrc]
  simp


theorem gc51_exists_remPath (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {V L : Finset ι}
    (hLV : L ⊆ V) {y g : W} (hyg : y ≠ g)
    (hVsrc : sources ends V = ({y, g} : Finset W)) (hLsrc : sources ends L = (∅ : Finset W)) :
    ∃ P, P ⊆ V \ L ∧ sources ends P = ({y, g} : Finset W) := by
  have hVLsrc : sources ends (V \ L) = ({y, g} : Finset W) :=
    gc51_sdiff_sources ends hLV hVsrc hLsrc
  
  have hyg_conn : connK ends (V \ L) y g := by
    apply path_exists ends (V \ L) (fun i _ => hnd i) y g
    · rw [← mem_sources, hVLsrc]; simp
    · intro z hz
      rw [← mem_sources, hVLsrc] at hz
      simpa using hz
    · exact hyg
  obtain ⟨P, hPsub, hPsrc⟩ := exists_conn_set ends (V \ L) hyg_conn hyg
  exact ⟨P, hPsub, hPsrc⟩


theorem gc51_remPath_disjoint {ι : Type*} [DecidableEq ι] {V L P : Finset ι}
    (hP : P ⊆ V \ L) : Disjoint L P := by
  rw [Finset.disjoint_left]
  intro i hiL hiP
  have := hP hiP
  rw [Finset.mem_sdiff] at this
  exact this.2 hiL


theorem gc51_mapsInto (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι)
    {o x y g : W} (hox : o ≠ x) (hyg : y ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {V L P : Finset ι} (hLV : L ⊆ V) (hPVL : P ⊆ V \ L)
    (hLsrc : sources ends L = (∅ : Finset W)) (hPsrc : sources ends P = ({y, g} : Finset W))
    (hgate : connK ends (K ∪ L) x g) :
    (L ∪ P) ⊆ V ∧ sources ends (L ∪ P) = ({y, g} : Finset W)
      ∧ connK ends (K ∪ (L ∪ P)) o x ∧ connK ends (K ∪ (L ∪ P)) o y
        ∧ connK ends (K ∪ (L ∪ P)) o g := by
  have hdisj : Disjoint L P := gc51_remPath_disjoint hPVL
  have hPV : P ⊆ V := fun i hi => (Finset.mem_sdiff.1 (hPVL hi)).1
  
  have hQV : (L ∪ P) ⊆ V := Finset.union_subset hLV hPV
  
  have hQsrc : sources ends (L ∪ P) = ({y, g} : Finset W) := by
    have hun : L ∪ P = L ∆ P := (Disjoint.symmDiff_eq_sup hdisj).symm
    rw [hun, sources_symmDiff, hLsrc, hPsrc]
    simp
  
  have hox_conn : connK ends (K ∪ (L ∪ P)) o x := by
    have hox_K : connK ends K o x := by
      apply path_exists ends K (fun i _ => hnd i) o x
      · rw [← mem_sources, hKsrc]; simp
      · intro z hz; rw [← mem_sources, hKsrc] at hz; simpa using hz
      · exact hox
    exact gc51_connK_mono ends (Finset.subset_union_left) hox_K
  have hxg_conn : connK ends (K ∪ (L ∪ P)) x g :=
    gc51_connK_mono ends (Finset.union_subset_union_right (Finset.subset_union_left)) hgate
  have hyg_conn : connK ends (K ∪ (L ∪ P)) y g := by
    have hyg_P : connK ends P y g := gc51_connK_of_sources ends hnd P hyg hPsrc
    have hPsub : P ⊆ K ∪ (L ∪ P) := by
      intro i hi; exact Finset.mem_union_right _ (Finset.mem_union_right _ hi)
    exact gc51_connK_mono ends hPsub hyg_P
  
  have hog_conn : connK ends (K ∪ (L ∪ P)) o g := hox_conn.trans hxg_conn
  have hoy_conn : connK ends (K ∪ (L ∪ P)) o y :=
    hog_conn.trans (connK_symm ends _ hyg_conn)
  exact ⟨hQV, hQsrc, hox_conn, hoy_conn, hog_conn⟩


end Abstract
end StatMech.Walls
