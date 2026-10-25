/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc71cyclespace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc70sharedsink.Part3
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


theorem gc71_room_of_gDeg1 (ends : ι → Sym2 W) {D : Finset ι} {g : W}
    (hge3 : 3 ≤ degK ends (univ : Finset ι) g) (hD1 : degK ends D g = 1) :
    2 ≤ degK ends ((univ : Finset ι) \ D) g :=
  gc65_gDegGe3_room ends hge3 hD1


theorem gc71_minConnector_gDeg1 (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {y g : W} (hyg : y ≠ g) {D : Finset ι} (hDV : D ⊆ univ \ K)
    (hDsrc : sources ends D = ({y, g} : Finset W))
    (hDmin : ∀ D', D' ⊆ univ \ K → sources ends D' = ({y, g} : Finset W) → #D ≤ #D') :
    degK ends D g = 1 :=
  gc69b_minConnector_gDeg1 ends hnd K hyg hDV hDsrc hDmin


theorem gc71_gc66_of_gDeg1Data (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hsurv : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g) :
    gc66_GDeg1RemovalSurvival ends K o x y g :=
  ⟨D, hDV, hDsrc, hD1, hsurv⟩


theorem gc71_countIneq_of_removalSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc66_GDeg1RemovalSurvival ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc66_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv h


end Abstract
end StatMech.Walls
