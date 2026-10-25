/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Switching.Part3
import Def.StatisticalMechanics.Code.Walls.menger_core.Part2
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

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm adjStep degK compOf
  sources_symmDiff mem_sources path_exists exists_conn_set)

open Classical


theorem mng_brg_conn : connK mng_brg (univ : Finset (Fin 2)) 0 2 :=
  (Relation.ReflTransGen.single (b := (1 : Fin 3))
      ⟨0, by decide, by decide, by decide, by decide⟩).trans
    (Relation.ReflTransGen.single (b := (2 : Fin 3))
      ⟨1, by decide, by decide, by decide, by decide⟩)


theorem mng_brg_univ_sources :
    sources mng_brg (univ : Finset (Fin 2)) = ({0, 2} : Finset (Fin 3)) := by decide


theorem mng_brg_delete_eq :
    (univ : Finset (Fin 2)) \ (univ : Finset (Fin 2)) = (∅ : Finset (Fin 2)) := by decide


theorem mng_brg_empty_disconn : ¬ connK mng_brg (∅ : Finset (Fin 2)) 0 2 := by
  intro h
  have inv : ∀ w : Fin 3, connK mng_brg (∅ : Finset (Fin 2)) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail b c _ hstep ih => obtain ⟨i, hi, _⟩ := hstep; simp at hi
  exact absurd (inv 2 h) (by decide)


theorem mng_test_bridge_no_two_disjoint :
    connK mng_brg (univ : Finset (Fin 2)) 0 2 ∧
    sources mng_brg (univ : Finset (Fin 2)) = ({0, 2} : Finset (Fin 3)) ∧
    ¬ connK mng_brg ((univ : Finset (Fin 2)) \ (univ : Finset (Fin 2))) 0 2 := by
  refine ⟨mng_brg_conn, mng_brg_univ_sources, ?_⟩
  rw [mng_brg_delete_eq]; exact mng_brg_empty_disconn


theorem mng_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
      {G : Finset ι} {a b : W} (hne : a ≠ b) (hab : connK ends G a b)
      (hab2 : ∀ P₁ : Finset ι, P₁ ⊆ G → sources ends P₁ = ({a, b} : Finset W) →
          connK ends (G \ P₁) a b),
      ∃ P₁ P₂ : Finset ι, P₁ ⊆ G ∧ P₂ ⊆ G ∧ Disjoint P₁ P₂ ∧
        sources ends P₁ = ({a, b} : Finset W) ∧ sources ends P₂ = ({a, b} : Finset W) ∧
        connK ends P₁ a b ∧ connK ends P₂ a b) ∧
    
    (∃ P₁ P₂ : Finset (Fin 4),
      P₁ ⊆ (univ : Finset (Fin 4)) ∧ P₂ ⊆ (univ : Finset (Fin 4)) ∧ Disjoint P₁ P₂ ∧
      connK mng_cyc P₁ 0 2 ∧ connK mng_cyc P₂ 0 2) ∧
    
    (¬ connK mng_brg ((univ : Finset (Fin 2)) \ (univ : Finset (Fin 2))) 0 2) :=
  ⟨fun ends hnd => mng_two_disjoint_connectors ends hnd,
   ⟨{0, 1}, {2, 3}, Finset.subset_univ _, Finset.subset_univ _, mng_cyc_disjoint,
     mng_cyc_P1_conn, mng_cyc_P2_conn⟩,
   by rw [mng_brg_delete_eq]; exact mng_brg_empty_disconn⟩

end StatMech.Walls
