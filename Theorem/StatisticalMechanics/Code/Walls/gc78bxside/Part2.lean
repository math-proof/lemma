/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc78bxside.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc77bdirect.Part2
import Def.StatisticalMechanics.Code.Walls.gc78bxside
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

open Classical


theorem gc78b_xEnds_loopless : ∀ i : Fin 7, ¬ (gc78b_xEnds i).IsDiag := by decide


theorem gc78b_xEnds_univ_sources :
    sources gc78b_xEnds (univ : Finset (Fin 7)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by decide


theorem gc78b_xEnds_K_sources :
    sources gc78b_xEnds ({2} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5)) := by decide


theorem gc78b_xEnds_g_deg3 : degK gc78b_xEnds (univ : Finset (Fin 7)) 3 = 3 := by decide


theorem gc78b_xEnds_og_not_in_K :
    ¬ connK gc78b_xEnds ({2} : Finset (Fin 7)) 0 3 := by
  intro h
  have inv : ∀ w : Fin 5, connK gc78b_xEnds ({2} : Finset (Fin 7)) 0 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)


theorem gc78b_xEnds_xg_not_in_K :
    ¬ connK gc78b_xEnds ({2} : Finset (Fin 7)) 1 3 := by
  intro h
  exact gc78b_xEnds_og_not_in_K
    ((gc78b_xg_in_K_iff_og_in_K gc78b_xEnds gc78b_xEnds_loopless (by decide)
      gc78b_xEnds_K_sources).1 h)


theorem gc78b_xEnds_L_sources :
    sources gc78b_xEnds ({0, 3, 5, 6} : Finset (Fin 7)) = (∅ : Finset (Fin 5)) := by decide


theorem gc78b_xEnds_gate :
    connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) 1 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7)))
        = ({0, 2, 3, 5, 6} : Finset (Fin 7)) from by decide]
  exact (Relation.ReflTransGen.single (b := (0 : Fin 5))
      ⟨2, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc78b_xEnds_mincardD_data :
    ({0, 3} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7))
      ∧ sources gc78b_xEnds ({0, 3} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5))
      ∧ degK gc78b_xEnds ({0, 3} : Finset (Fin 7)) 3 = 1 := by
  refine ⟨?_, by decide, by decide⟩
  rw [show (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7))
        = ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)) from by decide]
  decide


theorem gc78b_xEnds_workingD_data :
    ({5, 6} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7))
      ∧ sources gc78b_xEnds ({5, 6} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5))
      ∧ degK gc78b_xEnds ({5, 6} : Finset (Fin 7)) 3 = 1 := by
  refine ⟨?_, by decide, by decide⟩
  rw [show (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7))
        = ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)) from by decide]
  decide


theorem gc78b_mincard_D_fails_xg :
    ¬ connK gc78b_xEnds
      ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 1 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))
        = ({2, 5, 6} : Finset (Fin 7)) from by decide]
  intro h
  have inv : ∀ w : Fin 5, connK gc78b_xEnds ({2, 5, 6} : Finset (Fin 7)) 1 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)


theorem gc78b_mincard_D_fails_og :
    ¬ connK gc78b_xEnds
      ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 0 3 := by
  intro h
  exact gc78b_mincard_D_fails_xg
    ((gc78b_xgSurvives_iff_ogSurvives gc78b_xEnds gc78b_xEnds_loopless (o := 0) (x := 1)
      (by decide) gc78b_xEnds_K_sources
      (D := ({0, 3} : Finset (Fin 7)))
      (by rw [show (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7))
              = ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)) from by decide]; decide)).2 h)


theorem gc78b_working_D_works_xg :
    connK gc78b_xEnds
      ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 1 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
        = ({0, 2, 3} : Finset (Fin 7)) from by decide]
  exact (Relation.ReflTransGen.single (b := (0 : Fin 5))
      ⟨2, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc78b_xside_no_canonical_D :
    
    (({0, 3} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7))
        ∧ sources gc78b_xEnds ({0, 3} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5))
        ∧ degK gc78b_xEnds ({0, 3} : Finset (Fin 7)) 3 = 1)
      ∧ (({5, 6} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7))
        ∧ sources gc78b_xEnds ({5, 6} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5))
        ∧ degK gc78b_xEnds ({5, 6} : Finset (Fin 7)) 3 = 1)
      
      ∧ (¬ connK gc78b_xEnds
          ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7)))
            \ ({0, 3} : Finset (Fin 7))) 1 3)
      
      ∧ connK gc78b_xEnds
          ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7)))
            \ ({5, 6} : Finset (Fin 7))) 1 3 :=
  ⟨gc78b_xEnds_mincardD_data, gc78b_xEnds_workingD_data,
    gc78b_mincard_D_fails_xg, gc78b_working_D_works_xg⟩


theorem gc78b_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x g : W),
        o ≠ x → sources ends K = ({o, x} : Finset W) →
        (connK ends K x g ↔ connK ends K o g))
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        sources ends K = ({o, x} : Finset W) → connK ends K x g →
        gc71_TwoCommodityLeaf ends K o x y g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K L D : Finset ι) (o x g : W),
        o ≠ x → sources ends K = ({o, x} : Finset W) → D ⊆ univ \ K →
        (connK ends ((K ∪ L) \ D) x g ↔ connK ends ((K ∪ L) \ D) o g))
    ∧ 
    ((¬ connK gc78b_xEnds
        ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7)))
          \ ({0, 3} : Finset (Fin 7))) 1 3)
      ∧ connK gc78b_xEnds
          ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7)))
            \ ({5, 6} : Finset (Fin 7))) 1 3)
    ∧ 
    (¬ connK gc78b_xEnds ({2} : Finset (Fin 7)) 1 3) :=
  ⟨fun ends hnd K o x g hox hKsrc => gc78b_xg_in_K_iff_og_in_K ends hnd hox hKsrc,
    fun ends hnd K o x y g hox hoy hog hxy hxg hyg huniv hKsrc hxgK =>
      gc78b_twoCommodityLeaf_of_xgInK ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc hxgK,
    fun ends hnd K L D o x g hox hKsrc hDV =>
      gc78b_xgSurvives_iff_ogSurvives ends hnd hox hKsrc hDV,
    ⟨gc78b_mincard_D_fails_xg, gc78b_working_D_works_xg⟩,
    gc78b_xEnds_xg_not_in_K⟩

end StatMech.Walls
