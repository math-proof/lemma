/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc70sharedsink.Part3
import Def.StatisticalMechanics.Code.Walls.gc71cyclespace
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


theorem gc71_gc66_of_twoCommodityLeaf (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (h : gc71_TwoCommodityLeaf ends K o x y g) :
    gc66_GDeg1RemovalSurvival ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hD1, hL⟩ := h
  refine ⟨D, hDV, hDsrc, hD1, ?_⟩
  intro L hLmem
  obtain ⟨P, hPG, hPsrc, hPD, hPconn⟩ := hL L hLmem
  have hog' : connK ends ((K ∪ L) \ D) o g := mng_connK_of_disjoint ends hPG hPD hPconn
  exact gc68_xg_survives_of_og ends hnd hox hKsrc hDV hog'


theorem gc71_countIneq_of_twoCommodityLeaf (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc71_TwoCommodityLeaf ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc71_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv
  intro K hK
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  exact gc71_gc66_of_twoCommodityLeaf ends hnd K hox hKsrc (h K hK)

end Abstract
end StatMech.Walls
