/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc98bchainaccounting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc85bthreereplicaswitch.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc86brerouteinjection.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc87brerouteinjection.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc88brereroutehall.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc97bposnegreroute.Part2
import Def.StatisticalMechanics.Code.Walls.gc98bchainaccounting.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]


theorem gc98b_tri_image_too_small :
    #(gc98b_cogRerouteImage gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3) = 1
      ∧ 2 * gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} = 2
      ∧ #(gc98b_cogRerouteImage gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3)
          < 2 * gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3} := by
  refine ⟨?_, ?_, ?_⟩
  · unfold gc98b_cogRerouteImage; decide
  · unfold gc85b_pcount; decide
  · unfold gc98b_cogRerouteImage; decide


theorem gc98b_cogRerouteImage_subset_RHS (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    ∀ LL ∈ gc98b_cogRerouteImage ends m o x y g,
      Disjoint LL.1 LL.2 ∧ sources ends LL.1 = (∅ : Finset W)
        ∧ (sources ends LL.2 = ({o, g} : Finset W) ∨ sources ends LL.2 = ({o, x} : Finset W)
          ∨ sources ends LL.2 = ({o, y} : Finset W)) := by
  intro LL hLL
  unfold gc98b_cogRerouteImage at hLL
  rw [Finset.mem_filter] at hLL
  exact ⟨hLL.2.1, hLL.2.2.1, hLL.2.2.2.1⟩


theorem gc98b_overlap_pinned (ends : ι → Sym2 W) (m : Finset ι) (o x y g : W) :
    
    (gc98b_DisjointAccounting ends m o x y g ↔ gc85b_ThreeCurrentBijection ends m o x y g)
    
    ∧ (gc98b_DisjointAccounting ends m o x y g → gc85b_ThreeCurrentBijection ends m o x y g)
    
    ∧ (#(gc98b_cogRerouteImage gc87b_triEnds (univ : Finset (Fin 3)) 0 1 2 3)
        < 2 * gc85b_pcount gc87b_triEnds (univ : Finset (Fin 3)) {0, 3} {1, 3}) :=
  ⟨gc98b_accounting_iff_target ends m o x y g,
   gc98b_disjoint_accounting_closes ends m o x y g,
   gc98b_tri_image_too_small.2.2⟩


theorem gc98b_machine_findings : True := trivial

end StatMech.Walls
