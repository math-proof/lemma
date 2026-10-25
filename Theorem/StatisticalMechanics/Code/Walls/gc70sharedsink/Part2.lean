/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc70sharedsink.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc69mengerclose.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc65cyclespace.Part2
import Def.StatisticalMechanics.Code.Walls.gc70sharedsink
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


theorem gc70b_ogSurvival_of_ogConnAvoidingD (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (h : gc70b_OGConnAvoidingD ends K o x y g) :
    gc69b_OGSurvival ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hDmin, hL⟩ := h
  refine ⟨D, hDV, hDsrc, hDmin, ?_⟩
  intro L hLmem
  obtain ⟨P, hPG, hPsrc, hPD, hPconn⟩ := hL L hLmem
  exact gc70b_xgSurvival_of_disjointConnector ends hnd hox hKsrc hDV hPG hPD hPconn


theorem gc70b_ogConnAvoidingD_of_ogSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (h : gc69b_OGSurvival ends K o x y g) :
    gc70b_OGConnAvoidingD ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hDmin, hsurv⟩ := h
  refine ⟨D, hDV, hDsrc, hDmin, ?_⟩
  intro L hLmem
  have hxg : connK ends ((K ∪ L) \ D) x g := hsurv L hLmem
  have hog' : connK ends ((K ∪ L) \ D) o g :=
    (gc68_xg_iff_og_survives ends hnd hox hKsrc hDV).1 hxg
  obtain ⟨P, hPG, hPD, hPsrc, hPconn⟩ := gc69b_disjointConnector_of_ogReroute ends hnd hog hog'
  exact ⟨P, hPG, hPsrc, hPD, hPconn⟩


theorem gc70b_ogConnAvoidingD_iff_ogSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W)) :
    gc70b_OGConnAvoidingD ends K o x y g ↔ gc69b_OGSurvival ends K o x y g :=
  ⟨gc70b_ogSurvival_of_ogConnAvoidingD ends hnd K hox hKsrc,
    gc70b_ogConnAvoidingD_of_ogSurvival ends hnd K hox hog hKsrc⟩


theorem gc70b_countIneq_of_ogConnAvoidingD (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc70b_OGConnAvoidingD ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc69b_countIneq_of_ogSurvival ends hnd hox hoy hog hxy hxg hyg huniv
  intro K hK
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  exact gc70b_ogSurvival_of_ogConnAvoidingD ends hnd K hox hKsrc (h K hK)


theorem gc70b_sharedSink_disjoint_of_relConn (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {o g : W} (hog : o ≠ g) (hconn : mngg_RelConn ends G o g 2) :
    ∃ P₀ P₁ : Finset ι, P₀ ⊆ G ∧ P₁ ⊆ G ∧ Disjoint P₀ P₁ ∧
      connK ends P₀ o g ∧ connK ends P₁ o g ∧
      ∀ D : Finset ι, D ⊆ P₀ → connK ends (G \ D) o g := by
  obtain ⟨P, hsub, hsrc, hck, hdisj⟩ := mngg_edgeMenger ends hnd hog 2 hconn
  refine ⟨P 0, P 1, hsub 0, hsub 1, hdisj 0 1 (by decide), hck 0, hck 1, ?_⟩
  intro D hDP0
  
  have hP1D : Disjoint (P 1) D :=
    Finset.disjoint_of_subset_right hDP0 (hdisj 1 0 (by decide))
  exact mng_connK_of_disjoint ends (hsub 1) hP1D (hck 1)


theorem gc70b_sharedSink_survival (ends : ι → Sym2 W) {G D P : Finset ι} {o g : W}
    (hPG : P ⊆ G) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends (G \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn

end Abstract
end StatMech.Walls
