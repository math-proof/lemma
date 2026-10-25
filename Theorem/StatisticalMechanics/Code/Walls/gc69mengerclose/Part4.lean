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
import Def.StatisticalMechanics.Code.Walls.gc69mengerclose.Part3
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

open Classical


theorem gc69b_bridge_loopless : ∀ i : Fin 1, ¬ (gc69b_bridgeEnds i).IsDiag := by decide


theorem gc69b_bridge_isCut :
    mngg_IsCut gc69b_bridgeEnds (univ : Finset (Fin 1)) 0 1 ({0} : Finset (Fin 1)) := by
  refine ⟨by decide, ?_⟩
  intro h
  have hempty : (univ : Finset (Fin 1)) \ ({0} : Finset (Fin 1)) = (∅ : Finset (Fin 1)) := by decide
  rw [hempty] at h
  have inv : ∀ w : Fin 3, connK gc69b_bridgeEnds (∅ : Finset (Fin 1)) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail b c _ hstep ih => obtain ⟨i, hi, _⟩ := hstep; simp at hi
  exact absurd (inv 1 h) (by decide)


theorem gc69b_bridge_refutes_menger2 :
    ¬ mngg_RelConn gc69b_bridgeEnds (univ : Finset (Fin 1)) 0 1 2 :=
  gc69b_relConn2_false_of_bridge gc69b_bridgeEnds gc69b_bridge_loopless (by decide)
    gc69b_bridge_isCut (by decide)


theorem gc69b_refut_D12_min (D' : Finset (Fin 7))
    (hD'V : D' ⊆ (univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7)))
    (hD'src : sources gc63b_refutEnds D' = ({2, 3} : Finset (Fin 5))) :
    (#({1, 2} : Finset (Fin 7))) ≤ #D' := by
  rcases gc63b_connector_cases hD'V hD'src with rfl | rfl | rfl | rfl <;> decide


theorem gc69b_ogReroute_false :
    ¬ gc68_OGReroute gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 := by
  intro h
  
  have hDV : ({1, 2} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7)) := by decide
  have hDsrc : sources gc63b_refutEnds ({1, 2} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) := by decide
  have hLmem : ({1, 2, 5, 6} : Finset (Fin 7))
      ∈ gc51_LblockSet gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 3 := by
    rw [gc63b_refut_LblockSet]; decide
  have hsurv : connK gc63b_refutEnds
      ((({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) \ ({1, 2} : Finset (Fin 7))) 0 3 :=
    h ({1, 2} : Finset (Fin 7)) hDV hDsrc gc69b_refut_D12_min
      ({1, 2, 5, 6} : Finset (Fin 7)) hLmem
  rw [show (({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) \ ({1, 2} : Finset (Fin 7))
        = ({0, 5, 6} : Finset (Fin 7)) from by decide] at hsurv
  exact gc63b_iso_056_0.2 hsurv


theorem gc69b_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        o ≠ g →
        (gc68_OGReroute ends K o x y g ↔ gc69b_DisjointOGConnector ends K o x y g))
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W),
        o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
            gc69b_DisjointOGConnector ends K o x y g) →
        gc39_ThreeColouringCountIneq ends o x y g)
    ∧ 
    (¬ mngg_RelConn gc69b_bridgeEnds (univ : Finset (Fin 1)) 0 1 2)
    ∧ 
    (¬ gc68_OGReroute gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W),
        o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
            gc69b_OGSurvival ends K o x y g) →
        gc39_ThreeColouringCountIneq ends o x y g)
    ∧ 
    gc69b_DisjointOGConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc69b_OGSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends hnd K o x y g hog => gc69b_ogReroute_iff_disjointOGConnector ends hnd K hog,
    fun ends hnd o x y g hox hoy hog hxy hxg hyg huniv h =>
      gc69b_countIneq_of_disjointOGConnector ends hnd hox hoy hog hxy hxg hyg huniv h,
    gc69b_bridge_refutes_menger2,
    gc69b_ogReroute_false,
    fun ends hnd o x y g hox hoy hog hxy hxg hyg huniv h =>
      gc69b_countIneq_of_ogSurvival ends hnd hox hoy hog hxy hxg hyg huniv h,
    gc69b_witness_disjointOGConnector,
    gc69b_witness_ogSurvival,
    gc69b_witness_removalSurvival⟩

end StatMech.Walls
