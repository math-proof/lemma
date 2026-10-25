/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc77bdirect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc75bcyclespace
import Theorem.StatisticalMechanics.Code.Walls.gc67removable
import Def.StatisticalMechanics.Code.Walls.gc77bdirect
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


theorem gc77b_starEnds_loopless : ∀ i : Fin 6, ¬ (gc77b_starEnds i).IsDiag := by decide


theorem gc77b_starEnds_univ_sources :
    sources gc77b_starEnds (univ : Finset (Fin 6)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc77b_starEnds_K_sources :
    sources gc77b_starEnds ({0, 1, 2} : Finset (Fin 6)) = ({0, 1} : Finset (Fin 4)) := by decide


theorem gc77b_starEnds_g_deg : degK gc77b_starEnds (univ : Finset (Fin 6)) 3 = 5 := by decide


theorem gc77b_starEnds_og_in_K :
    connK gc77b_starEnds ({0, 1, 2} : Finset (Fin 6)) 0 3 :=
  (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨1, by decide, by decide, by decide, by decide⟩


theorem gc77b_star_twoCommodityLeaf :
    gc71_TwoCommodityLeaf gc77b_starEnds ({0, 1, 2} : Finset (Fin 6)) 0 1 2 3 :=
  gc77b_twoCommodityLeaf_of_ogInK gc77b_starEnds gc77b_starEnds_loopless
    ({0, 1, 2} : Finset (Fin 6)) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc77b_starEnds_univ_sources gc77b_starEnds_K_sources gc77b_starEnds_og_in_K


theorem gc77b_hard_twoCommodity_content :
    (¬ connK gc74b_brEnds2
        ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3)
      ∧ connK gc74b_brEnds2
          ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3 :=
  gc74b_bridge_twoCommodity_content


theorem gc77b_hard_og_not_in_K :
    ¬ connK gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 3 := by
  intro h
  have inv : ∀ w : Fin 4, connK gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)


theorem gc77b_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x : W),
        o ≠ x → sources ends K = ({o, x} : Finset W) → connK ends K o x)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        sources ends K = ({o, x} : Finset W) → connK ends K o g →
        gc71_TwoCommodityLeaf ends K o x y g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K L D : Finset ι) (o x g : W),
        o ≠ x → sources ends K = ({o, x} : Finset W) → D ⊆ univ \ K →
        (connK ends ((K ∪ L) \ D) x g ↔ connK ends ((K ∪ L) \ D) o g))
    ∧ 
    gc71_TwoCommodityLeaf gc77b_starEnds ({0, 1, 2} : Finset (Fin 6)) 0 1 2 3
    ∧ 
    ((¬ connK gc74b_brEnds2
        ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3)
      ∧ connK gc74b_brEnds2
          ((({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5))) \ ({3} : Finset (Fin 5))) 0 3) :=
  ⟨fun ends hnd K o x hox hKsrc => gc77b_ox_in_K ends hnd hox hKsrc,
    fun ends hnd K o x y g hoy hog hxy hxg hyg huniv hKsrc hogK =>
      gc77b_twoCommodityLeaf_of_ogInK ends hnd K hoy hog hxy hxg hyg huniv hKsrc hogK,
    fun ends hnd K L D o x g hox hKsrc hDV =>
      gc77b_ogSurvives_iff_xgSurvives ends hnd hox hKsrc hDV,
    gc77b_star_twoCommodityLeaf,
    gc77b_hard_twoCommodity_content⟩

end StatMech.Walls
