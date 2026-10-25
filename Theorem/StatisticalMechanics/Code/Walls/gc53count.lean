/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc53count.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc52switchinj.Part2
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


theorem gc53_ox_conn_of_sources (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x : W} (hox : o ≠ x) (hKsrc : sources ends K = ({o, x} : Finset W)) :
    connK ends K o x := by
  apply path_exists ends K (fun i _ => hnd i) o x
  · rw [← mem_sources, hKsrc]; simp
  · intro z hz; rw [← mem_sources, hKsrc] at hz; simpa using hz
  · exact hox


theorem gc53_allConn_iff_xg_gate (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K Q : Finset ι) {o x y g : W} (hox : o ≠ x) (hyg : y ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hQsrc : sources ends Q = ({y, g} : Finset W)) :
    (connK ends (K ∪ Q) o x ∧ connK ends (K ∪ Q) o y ∧ connK ends (K ∪ Q) o g)
      ↔ connK ends (K ∪ Q) x g := by
  have hox_conn : connK ends (K ∪ Q) o x :=
    gc51_connK_mono ends Finset.subset_union_left
      (gc53_ox_conn_of_sources ends hnd K hox hKsrc)
  have hyg_conn : connK ends (K ∪ Q) y g :=
    gc51_connK_mono ends Finset.subset_union_right
      (gc51_connK_of_sources ends hnd Q hyg hQsrc)
  constructor
  · rintro ⟨_, _, hog⟩
    
    exact (connK_symm ends _ hox_conn).trans hog
  · intro hxg
    
    have hog : connK ends (K ∪ Q) o g := hox_conn.trans hxg
    have hoy : connK ends (K ∪ Q) o y := hog.trans (connK_symm ends _ hyg_conn)
    exact ⟨hox_conn, hoy, hog⟩


theorem gc53_Rblock_eq_gateBlock (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hyg : y ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W)) :
    gc51_RblockSet ends K o x y g
      = (univ \ K).powerset.filter
          (fun Q => sources ends Q = ({y, g} : Finset W) ∧ connK ends (K ∪ Q) x g) := by
  rw [gc51_RblockSet]
  apply Finset.filter_congr
  intro Q hQ
  by_cases hQsrc : sources ends Q = ({y, g} : Finset W)
  · 
    have hiff := gc53_allConn_iff_xg_gate ends hnd K Q hox hyg hKsrc hQsrc
    constructor
    · rintro ⟨_, hax, hay, hag⟩; exact ⟨hQsrc, hiff.1 ⟨hax, hay, hag⟩⟩
    · rintro ⟨_, hxg⟩; obtain ⟨hax, hay, hag⟩ := hiff.2 hxg; exact ⟨hQsrc, hax, hay, hag⟩
  · 
    constructor
    · rintro ⟨h, _⟩; exact absurd h hQsrc
    · rintro ⟨h, _⟩; exact absurd h hQsrc


theorem gc53_exists_fixedPath (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι)
    {o x y g : W} (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W)) :
    ∃ P₀, P₀ ⊆ univ \ K ∧ sources ends P₀ = ({y, g} : Finset W) := by
  have hVsrc : sources ends (univ \ K) = ({y, g} : Finset W) :=
    gc51_complSources ends K hoy hog hxy hxg huniv hKsrc
  have hyg_conn : connK ends (univ \ K) y g := by
    apply path_exists ends (univ \ K) (fun i _ => hnd i) y g
    · rw [← mem_sources, hVsrc]; simp
    · intro z hz; rw [← mem_sources, hVsrc] at hz; simpa using hz
    · exact hyg
  obtain ⟨P₀, hP₀sub, hP₀src⟩ := exists_conn_set ends (univ \ K) hyg_conn hyg
  exact ⟨P₀, hP₀sub, hP₀src⟩


end Abstract
end StatMech.Walls
