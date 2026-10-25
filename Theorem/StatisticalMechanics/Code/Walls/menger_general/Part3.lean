/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
import Def.StatisticalMechanics.Code.Walls.menger_general.Part3
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

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]


theorem mngg_RelConn_of_le {ends : ι → Sym2 W} {G : Finset ι} {a b : W} {k k' : ℕ}
    (hkk' : k ≤ k') (h : mngg_RelConn ends G a b k') : mngg_RelConn ends G a b k :=
  fun j hj P hP => h j (lt_of_lt_of_le hj hkk') P hP


theorem mngg_augment (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) {j : ℕ} {P : Fin j → Finset ι}
    (hP : mngg_DisjointFamily ends G a b P)
    (hres : connK ends (G \ mngg_familyUnion P) a b) :
    ∃ Q : Fin (j + 1) → Finset ι, mngg_DisjointFamily ends G a b Q ∧
      (∀ i : Fin j, Q i.castSucc = P i) ∧ Q (Fin.last j) ⊆ G \ mngg_familyUnion P := by
  
  obtain ⟨Q₀, hQ₀sub, hQ₀src⟩ := exists_conn_set ends (G \ mngg_familyUnion P) hres hab
  
  have hQ₀src' : sources ends Q₀ = ({a, b} : Finset W) := by
    rw [hQ₀src]
  
  have hQ₀G : Q₀ ⊆ G := fun x hx => (Finset.mem_sdiff.1 (hQ₀sub hx)).1
  
  have hQ₀disjU : Disjoint Q₀ (mngg_familyUnion P) := by
    rw [Finset.disjoint_left]
    intro x hx
    exact (Finset.mem_sdiff.1 (hQ₀sub hx)).2
  refine ⟨Fin.snoc P Q₀, ⟨?_, ?_⟩, ?_, ?_⟩
  · 
    intro i
    refine Fin.lastCases ?_ ?_ i
    · rw [Fin.snoc_last]; exact ⟨hQ₀G, hQ₀src'⟩
    · intro i'; rw [Fin.snoc_castSucc]; exact hP.1 i'
  · 
    intro i i'
    refine Fin.lastCases ?_ ?_ i
    · 
      refine Fin.lastCases ?_ ?_ i'
      · intro hne; exact absurd rfl hne
      · intro i'' _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        refine Finset.disjoint_of_subset_right ?_ hQ₀disjU
        intro x hx; rw [mngg_mem_familyUnion]; exact ⟨i'', hx⟩
    · intro i''
      refine Fin.lastCases ?_ ?_ i'
      · intro _
        rw [Fin.snoc_last, Fin.snoc_castSucc]
        refine Finset.disjoint_of_subset_left ?_ hQ₀disjU.symm
        intro x hx; rw [mngg_mem_familyUnion]; exact ⟨i'', hx⟩
      · intro i''' hne
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
        refine hP.2 i'' i''' ?_
        intro h; exact hne (by rw [h])
  · intro i; rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last]; exact hQ₀sub


theorem mngg_edgeMenger_family (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) (k : ℕ)
    (hconn : mngg_RelConn ends G a b k) :
    ∃ P : Fin k → Finset ι, mngg_DisjointFamily ends G a b P := by
  induction k with
  | zero =>
    exact ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    
    obtain ⟨P, hP⟩ := ih (mngg_RelConn_of_le (Nat.le_succ n) hconn)
    
    have hres : connK ends (G \ mngg_familyUnion P) a b :=
      hconn n (Nat.lt_succ_self n) P hP
    
    obtain ⟨Q, hQ, _, _⟩ := mngg_augment ends hnd hab hP hres
    exact ⟨Q, hQ⟩


theorem mngg_edgeMenger (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) (k : ℕ)
    (hconn : mngg_RelConn ends G a b k) :
    ∃ P : Fin k → Finset ι,
      (∀ i, P i ⊆ G) ∧
      (∀ i, sources ends (P i) = ({a, b} : Finset W)) ∧
      (∀ i, connK ends (P i) a b) ∧
      (∀ i i', i ≠ i' → Disjoint (P i) (P i')) := by
  obtain ⟨P, hconn', hdisj⟩ := mngg_edgeMenger_family ends hnd hab k hconn
  refine ⟨P, fun i => (hconn' i).1, fun i => (hconn' i).2, ?_, hdisj⟩
  intro i
  exact mngg_connK_of_isConnector ends hnd hab (hconn' i)


end Abstract
end StatMech.Walls
