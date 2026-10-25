/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
import Def.StatisticalMechanics.Code.Walls.menger_general.Part7
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


theorem mngg_sq_cut_disconnects :
    ¬ connK mngg_sq ((univ : Finset (Fin 4)) \ mngg_sq_cut) 0 2 := by
  intro h
  have inv : ∀ w : Fin 4,
      connK mngg_sq ((univ : Finset (Fin 4)) \ mngg_sq_cut) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hc, hd, hcd⟩ := hstep
      revert hc hd hcd ih
      fin_cases i <;> simp_all [mngg_sq, mngg_sq_cut]
  exact absurd (inv 2 h) (by decide)


theorem mngg_test_square_not_three :
    mngg_IsCut mngg_sq (univ : Finset (Fin 4)) 0 2 mngg_sq_cut ∧
    #mngg_sq_cut = 2 ∧
    (∀ (P : Fin 3 → Finset (Fin 4)),
      mngg_DisjointFamily mngg_sq (univ : Finset (Fin 4)) 0 2 P → False) := by
  have hcut : mngg_IsCut mngg_sq (univ : Finset (Fin 4)) 0 2 mngg_sq_cut :=
    ⟨by decide, mngg_sq_cut_disconnects⟩
  have hloop : ∀ i : Fin 4, ¬ (mngg_sq i).IsDiag := by decide
  refine ⟨hcut, by decide, ?_⟩
  intro P hP
  have : (3 : ℕ) ≤ #mngg_sq_cut :=
    mngg_card_cut_ge mngg_sq hloop (by decide) hP hcut
  rw [show #mngg_sq_cut = 2 from by decide] at this
  omega


theorem mngg_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
      {G : Finset ι} {a b : W} (hab : a ≠ b) (k : ℕ) (hconn : mngg_RelConn ends G a b k),
      ∃ P : Fin k → Finset ι, mngg_DisjointFamily ends G a b P) ∧
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
      {G : Finset ι} {a b : W} (hab : a ≠ b) {k : ℕ} {P : Fin k → Finset ι}
      (hP : mngg_DisjointFamily ends G a b P) {C : Finset ι} (hC : mngg_IsCut ends G a b C),
      k ≤ #C) ∧
    
    (∃ P₁ P₂ P₃ : Finset (Fin 6),
      Disjoint P₁ P₂ ∧ Disjoint P₁ P₃ ∧ Disjoint P₂ P₃ ∧
      connK mngg_theta P₁ 0 4 ∧ connK mngg_theta P₂ 0 4 ∧ connK mngg_theta P₃ 0 4) ∧
    
    (∀ (P : Fin 3 → Finset (Fin 4)),
      mngg_DisjointFamily mngg_sq (univ : Finset (Fin 4)) 0 2 P → False) := by
  refine ⟨?_, ?_, ?_, mngg_test_square_not_three.2.2⟩
  · intro ι W _ _ _ _ ends hnd G a b hab k hconn
    exact mngg_edgeMenger_family ends hnd hab k hconn
  · intro ι W _ _ _ _ ends hnd G a b hab k P hP C hC
    exact mngg_card_cut_ge ends hnd hab hP hC
  · exact ⟨{0}, {1, 2}, {3, 4, 5}, mngg_theta_disjoint.1, mngg_theta_disjoint.2.1,
      mngg_theta_disjoint.2.2, mngg_theta_P1_conn, mngg_theta_P2_conn, mngg_theta_P3_conn⟩

end StatMech.Walls
