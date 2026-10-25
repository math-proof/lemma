/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc51minpath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc50threereplica.Part3
import Def.StatisticalMechanics.Code.Walls.gc51minpath.Part3
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

open Classical


theorem gc51_ceEnds_univ_sources :
    sources gc51_ceEnds (univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 4)) := by decide


theorem gc51_ce_Rblock_zero :
    gc50_Rblock gc51_ceEnds ({0, 1} : Finset (Fin 2)) 0 1 2 3 = 0 := by
  rw [gc50_Rblock]
  have hV : (univ : Finset (Fin 2)) \ ({0, 1} : Finset (Fin 2)) = (∅ : Finset (Fin 2)) := by decide
  rw [hV]; decide


theorem gc51_ce_Lblock_one :
    gc50_Lblock gc51_ceEnds ({0, 1} : Finset (Fin 2)) 0 1 3 = 1 := by
  rw [gc50_Lblock]
  have hV : (univ : Finset (Fin 2)) \ ({0, 1} : Finset (Fin 2)) = (∅ : Finset (Fin 2)) := by decide
  rw [hV]
  have hset : (∅ : Finset (Fin 2)).powerset.filter
      (fun L => sources gc51_ceEnds L = (∅ : Finset (Fin 4))) = {(∅ : Finset (Fin 2))} := by decide
  rw [show (∅ : Finset (Fin 2)).powerset.filter
        (fun L => sources gc51_ceEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc51_ceEnds (({0, 1} : Finset (Fin 2)) ∪ L) 1 3)
      = ((∅ : Finset (Fin 2)).powerset.filter
          (fun L => sources gc51_ceEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc51_ceEnds (({0, 1} : Finset (Fin 2)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hconn : connK gc51_ceEnds (({0, 1} : Finset (Fin 2)) ∪ (∅ : Finset (Fin 2))) 1 3 := by
    rw [Finset.union_empty]
    exact Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_singleton, if_pos hconn, Finset.card_singleton]


theorem gc51_perKDom_false_without_huniv :
    ¬ gc50_PerKDom gc51_ceEnds (0 : Fin 4) 1 2 3 := by
  intro h
  have hK : ({0, 1} : Finset (Fin 2)) ∈ (univ : Finset (Fin 2)).powerset.filter
      (fun K => sources gc51_ceEnds K = ({0, 1} : Finset (Fin 4))) := by decide
  have hle := h ({0, 1} : Finset (Fin 2)) hK
  rw [gc51_ce_Lblock_one, gc51_ce_Rblock_zero] at hle
  exact absurd hle (by norm_num)

end StatMech.Walls
