/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc68removalsurvival.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc67removable
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
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


theorem gc68_K_survives {K L D : Finset ι} (hDV : D ⊆ univ \ K) :
    K ⊆ (K ∪ L) \ D := by
  intro i hiK
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_union_left _ hiK, ?_⟩
  intro hiD
  exact (Finset.mem_sdiff.1 (hDV hiD)).2 hiK


theorem gc68_ox_survives (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o x : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W)) (hDV : D ⊆ univ \ K) :
    connK ends ((K ∪ L) \ D) o x := by
  have hoxK : connK ends K o x := by
    apply path_exists ends K (fun i _ => hnd i) o x
    · rw [← mem_sources, hKsrc]; simp
    · intro z hz; rw [← mem_sources, hKsrc] at hz; simpa using hz
    · exact hox
  exact mng_connK_mono ends (gc68_K_survives hDV) hoxK


theorem gc68_xg_iff_og_survives (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o x g : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W)) (hDV : D ⊆ univ \ K) :
    connK ends ((K ∪ L) \ D) x g ↔ connK ends ((K ∪ L) \ D) o g := by
  have hox' : connK ends ((K ∪ L) \ D) o x := gc68_ox_survives ends hnd hox hKsrc hDV
  constructor
  · intro hxg; exact hox'.trans hxg
  · intro hog; exact (connK_symm ends _ hox').trans hog


theorem gc68_xg_survives_of_og (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o x g : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W)) (hDV : D ⊆ univ \ K)
    (hog : connK ends ((K ∪ L) \ D) o g) :
    connK ends ((K ∪ L) \ D) x g :=
  (gc68_xg_iff_og_survives ends hnd hox hKsrc hDV).2 hog


theorem gc68b_xg_avoids_D_of_disjointConnector (ends : ι → Sym2 W) {K L D P : Finset ι} {x g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P x g) :
    connK ends ((K ∪ L) \ D) x g :=
  mng_connK_of_disjoint ends hPG hPD hPconn


theorem gc68b_xg_avoids_D_of_boundaryConnector (ends : ι → Sym2 W) {K L D P : Finset ι} {x g : W}
    (hPG : P ⊆ K ∪ L) (hPsrc : sources ends P = ({x, g} : Finset W)) (hPD : Disjoint P D)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (hxg : x ≠ g) :
    connK ends ((K ∪ L) \ D) x g := by
  have hPconn : connK ends P x g := by
    apply path_exists ends P (fun i _ => hnd i) x g
    · rw [← mem_sources, hPsrc]; simp
    · intro z hz; rw [← mem_sources, hPsrc] at hz; simpa using hz
    · exact hxg
  exact gc68b_xg_avoids_D_of_disjointConnector ends hPG hPD hPconn


end Abstract
end StatMech.Walls
