/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/menger_general.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.menger_core.Part3
import Def.StatisticalMechanics.Code.Walls.menger_general.Part4
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


theorem mngg_cut_meets_connector (ends : ι → Sym2 W) {G : Finset ι} {a b : W} {C P : Finset ι}
    (hC : mngg_IsCut ends G a b C) (hPG : P ⊆ G) (hPconn : connK ends P a b) :
    (P ∩ C).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hempty
  exact hC.2 (mng_connK_of_disjoint ends hPG hempty hPconn)


theorem mngg_card_cut_ge (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) {k : ℕ} {P : Fin k → Finset ι}
    (hP : mngg_DisjointFamily ends G a b P) {C : Finset ι} (hC : mngg_IsCut ends G a b C) :
    k ≤ #C := by
  
  have hmeet : ∀ i, ((P i) ∩ C).Nonempty := fun i =>
    mngg_cut_meets_connector ends hC (hP.1 i).1
      (mngg_connK_of_isConnector ends hnd hab (hP.1 i))
  choose e he using hmeet
  have heC : ∀ i, e i ∈ C := fun i => (Finset.mem_inter.1 (he i)).2
  have heP : ∀ i, e i ∈ P i := fun i => (Finset.mem_inter.1 (he i)).1
  
  have hinj : Function.Injective e := by
    intro i i' h
    by_contra hne
    exact (Finset.disjoint_left.1 (hP.2 i i' hne)) (heP i) (h ▸ heP i')
  
  have hle := Finset.card_le_card_of_injOn (s := (Finset.univ : Finset (Fin k))) (t := C) e
    (fun i _ => heC i) (fun i _ i' _ h => hinj h)
  simpa using hle


theorem mngg_three_disjoint_connectors (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) (hconn : mngg_RelConn ends G a b 3) :
    ∃ P₁ P₂ P₃ : Finset ι,
      P₁ ⊆ G ∧ P₂ ⊆ G ∧ P₃ ⊆ G ∧
      Disjoint P₁ P₂ ∧ Disjoint P₁ P₃ ∧ Disjoint P₂ P₃ ∧
      sources ends P₁ = ({a, b} : Finset W) ∧
      sources ends P₂ = ({a, b} : Finset W) ∧
      sources ends P₃ = ({a, b} : Finset W) ∧
      connK ends P₁ a b ∧ connK ends P₂ a b ∧ connK ends P₃ a b := by
  obtain ⟨P, hsub, hsrc, hck, hdisj⟩ := mngg_edgeMenger ends hnd hab 3 hconn
  refine ⟨P 0, P 1, P 2, hsub 0, hsub 1, hsub 2, ?_, ?_, ?_,
    hsrc 0, hsrc 1, hsrc 2, hck 0, hck 1, hck 2⟩
  · exact hdisj 0 1 (by decide)
  · exact hdisj 0 2 (by decide)
  · exact hdisj 1 2 (by decide)


theorem mngg_maxflow_mincut (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hab : a ≠ b) (k : ℕ)
    (hconn : mngg_RelConn ends G a b k) :
    (∃ P : Fin k → Finset ι, mngg_DisjointFamily ends G a b P) ∧
    (∀ C : Finset ι, mngg_IsCut ends G a b C → k ≤ #C) := by
  obtain ⟨P, hP⟩ := mngg_edgeMenger_family ends hnd hab k hconn
  exact ⟨⟨P, hP⟩, fun C hC => mngg_card_cut_ge ends hnd hab hP hC⟩


theorem mngg_disjoint_connectors_of_cut (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {x g : W} (hne : x ≠ g) (k : ℕ)
    (hconn : mngg_RelConn ends G x g (k + 1)) :
    ∃ (P₀ : Finset ι) (P : Fin k → Finset ι),
      P₀ ⊆ G ∧ connK ends P₀ x g ∧ (∀ i, P i ⊆ G) ∧ (∀ i, connK ends (P i) x g) ∧
      (∀ i, Disjoint P₀ (P i)) ∧ (∀ i i', i ≠ i' → Disjoint (P i) (P i')) ∧
      (∀ D : Finset ι, D ⊆ mngg_familyUnion P → connK ends (G \ D) x g) := by
  obtain ⟨Q, hsub, hsrc, hck, hdisj⟩ := mngg_edgeMenger ends hnd hne (k + 1) hconn
  
  refine ⟨Q (Fin.last k), fun i => Q i.castSucc,
    hsub _, hck _, fun i => hsub _, fun i => hck _, ?_, ?_, ?_⟩
  · 
    intro i
    exact hdisj (Fin.last k) i.castSucc (by
      intro h; exact absurd h.symm (Fin.castSucc_lt_last i).ne)
  · 
    intro i i' hii'
    exact hdisj i.castSucc i'.castSucc (by
      intro h; exact hii' (Fin.castSucc_injective _ h))
  · 
    intro D hD
    have hP₀U : Disjoint (Q (Fin.last k)) (mngg_familyUnion (fun i => Q i.castSucc)) := by
      rw [Finset.disjoint_left]
      intro y hy hyU
      rw [mngg_mem_familyUnion] at hyU
      obtain ⟨i, hi⟩ := hyU
      exact (Finset.disjoint_left.1
        (hdisj (Fin.last k) i.castSucc (by
          intro h; exact absurd h.symm (Fin.castSucc_lt_last i).ne))) hy hi
    have hP₀D : Disjoint (Q (Fin.last k)) D :=
      Finset.disjoint_of_subset_right hD hP₀U
    exact mng_connK_of_disjoint ends (hsub _) hP₀D (hck _)

end Abstract
end StatMech.Walls
