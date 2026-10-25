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
import Def.StatisticalMechanics.Code.Walls.gc69mengerclose
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


theorem gc69b_ogReroute_of_disjointOGConnector (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc69b_DisjointOGConnector ends K o x y g) :
    gc68_OGReroute ends K o x y g := by
  intro D hDV hDsrc hDmin L hL
  obtain ⟨P, hPG, hPsrc, hPD, hPconn⟩ := h D hDV hDsrc hDmin L hL
  exact gc69b_ogReroute_of_disjointConnector ends hPG hPD hPconn


theorem gc69b_disjointOGConnector_of_ogReroute (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W} (hog : o ≠ g)
    (h : gc68_OGReroute ends K o x y g) :
    gc69b_DisjointOGConnector ends K o x y g := by
  intro D hDV hDsrc hDmin L hL
  have hsurv : connK ends ((K ∪ L) \ D) o g := h D hDV hDsrc hDmin L hL
  obtain ⟨P, hPG, hPD, hPsrc, hPconn⟩ := gc69b_disjointConnector_of_ogReroute ends hnd hog hsurv
  exact ⟨P, hPG, hPsrc, hPD, hPconn⟩


theorem gc69b_ogReroute_iff_disjointOGConnector (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W} (hog : o ≠ g) :
    gc68_OGReroute ends K o x y g ↔ gc69b_DisjointOGConnector ends K o x y g :=
  ⟨gc69b_disjointOGConnector_of_ogReroute ends hnd K hog,
    gc69b_ogReroute_of_disjointOGConnector ends K⟩


theorem gc69b_removalSurvival_of_disjointOGConnector (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (h : gc69b_DisjointOGConnector ends K o x y g) :
    gc66_GDeg1RemovalSurvival ends K o x y g :=
  gc68_removalSurvival_of_ogReroute ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc
    (gc69b_ogReroute_of_disjointOGConnector ends K h)


theorem gc69b_countIneq_of_disjointOGConnector (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc69b_DisjointOGConnector ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc68_countIneq_of_ogReroute ends hnd hox hoy hog hxy hxg hyg huniv
  intro K hK
  exact gc69b_ogReroute_of_disjointOGConnector ends K (h K hK)


end Abstract
end StatMech.Walls
