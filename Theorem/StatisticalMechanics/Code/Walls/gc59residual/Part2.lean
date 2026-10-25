/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc59residual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc58cyclespace
import Def.StatisticalMechanics.Code.Walls.gc59residual
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
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000


namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem gc59_connK_of_peelable (ends : ι → Sym2 W) {a b : W} :
    ∀ (ds : List ι) (G : Finset ι), gc59_Peelable ends G ds → connK ends G a b →
      connK ends (gc59_removeList G ds) a b := by
  intro ds
  induction ds with
  | nil => intro G _ hab; simpa [gc59_removeList] using hab
  | cons i rest ih =>
    intro G hpeel hab
    obtain ⟨hiG, ⟨p, q, hpq, hconn⟩, hrest⟩ := hpeel
    have hstep : connK ends (G \ {i}) a b :=
      gc59_reroute_step ends G i hiG hpq hconn hab
    simpa [gc59_removeList] using ih (G \ {i}) hrest hstep


theorem gc59_removeList_eq_sdiff (G : Finset ι) (ds : List ι) :
    gc59_removeList G ds = G \ ds.toFinset := by
  induction ds generalizing G with
  | nil => simp [gc59_removeList]
  | cons i rest ih =>
    rw [gc59_removeList, ih]
    ext j
    simp only [Finset.mem_sdiff, List.toFinset_cons, Finset.mem_insert, Finset.mem_singleton,
      List.mem_toFinset]
    tauto


theorem gc59_connK_of_peelable_sdiff (ends : ι → Sym2 W) {a b : W} (G : Finset ι) (ds : List ι)
    (hpeel : gc59_Peelable ends G ds) (hab : connK ends G a b) :
    connK ends (G \ ds.toFinset) a b := by
  rw [← gc59_removeList_eq_sdiff]
  exact gc59_connK_of_peelable ends ds G hpeel hab


theorem gc59_sdiff_inter (G D : Finset ι) : G \ (D ∩ G) = G \ D := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_inter]
  tauto


theorem gc59_gate_survives_of_peeling (ends : ι → Sym2 W) {K L D : Finset ι} {x g : W}
    {ds : List ι} (hds : ds.toFinset = D ∩ (K ∪ L))
    (hpeel : gc59_Peelable ends (K ∪ L) ds) (hgate : connK ends (K ∪ L) x g) :
    connK ends ((K ∪ L) \ D) x g := by
  have := gc59_connK_of_peelable_sdiff ends (K ∪ L) ds hpeel hgate
  rw [hds, gc59_sdiff_inter] at this
  exact this


end Abstract
end StatMech.Walls
