/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/WhitneyCorrect.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarFaceGeometric.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanBridgeCycle.Part10
import Def.StatisticalMechanics.Code.Lattice.WhitneyCorrect.Part5
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem whc_phiWitness_iff (x : Site 2) : whc_phiWitness x ↔ (x 0 = 0 ∧ x 1 = 0) := by
  unfold whc_phiWitness; rw [whc_site_eq_iff]


theorem whc_square_adj_cases {u v : Site 2} (h : (imageGraph jbc_Pce).Adj u v) :
    (u = ![(0:ℤ), 0] ∧ v = ![1, 0]) ∨ (u = ![(1:ℤ), 0] ∧ v = ![0, 0]) ∨
    (u = ![(1:ℤ), 0] ∧ v = ![1, 1]) ∨ (u = ![(1:ℤ), 1] ∧ v = ![1, 0]) ∨
    (u = ![(1:ℤ), 1] ∧ v = ![0, 1]) ∨ (u = ![(0:ℤ), 1] ∧ v = ![1, 1]) ∨
    (u = ![(0:ℤ), 1] ∧ v = ![0, 0]) ∨ (u = ![(0:ℤ), 0] ∧ v = ![0, 1]) := by
  obtain ⟨i, j, hadj, hu, hv⟩ := h
  have hadj' : jbc_cyc4Rel i j = true := hadj
  have hu' : jbc_csq i = u := hu
  have hv' : jbc_csq j = v := hv
  subst hu'; subst hv'
  revert hadj'
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => k.elim0)))) i <;>
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun k => k.elim0)))) j <;>
    intro hadj' <;> first
      | (exact absurd hadj' (by decide))
      | (simp only [jbc_csq]; tauto)


theorem whc_square_mem_iff (e : Sym2 (Site 2)) :
    e ∈ (imageGraph jbc_Pce).edgeSet ↔
      e = s(![(0:ℤ), 0], ![1, 0]) ∨ e = s(![(1:ℤ), 0], ![1, 1]) ∨
      e = s(![(1:ℤ), 1], ![0, 1]) ∨ e = s(![(0:ℤ), 1], ![0, 0]) := by
  induction e with
  | h u v =>
    rw [SimpleGraph.mem_edgeSet]
    constructor
    · intro h
      rcases whc_square_adj_cases h with
        ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
        simp only [Sym2.eq_iff] <;> tauto
    · intro h
      obtain ⟨i, j, ha, hb, hc⟩ :
          ∃ x y : Fin 4, jbc_cyc4.Adj x y ∧ jbc_csq x = u ∧ jbc_csq y = v := by
        rcases h with h|h|h|h <;> rw [Sym2.eq_iff] at h <;> rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
        · exact ⟨0, 1, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨1, 0, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨1, 2, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨2, 1, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨2, 3, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨3, 2, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨3, 0, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
        · exact ⟨0, 3, by rw [jbc_cyc4_adj]; decide, rfl, rfl⟩
      exact ⟨i, j, ha, hb, hc⟩


theorem whc_shared_mem_square_iff (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    sharedPrimalEdge a b ∈ (imageGraph jbc_Pce).edgeSet ↔
      (s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1]) ∨ s(a, b) = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∨
       s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), 1]) ∨ s(a, b) = s(![(0:ℤ), 0], ![(-1:ℤ), 0])) := by
  rw [whc_square_mem_iff, whc_inv_bottom a b hab, whc_inv_right a b hab, whc_inv_top a b hab,
    whc_inv_left a b hab]

theorem whc_Htest_mem (e : Sym2 (Site 2)) :
    e ∈ whc_Htest.edgeSet ↔
      e ∈ (imageGraph jbc_Pce).edgeSet ∧ e ≠ s(![(0:ℤ), 0], ![1, 0]) := by
  unfold whc_Htest
  rw [SimpleGraph.edgeSet_deleteEdges, Set.mem_diff, Set.mem_singleton_iff]


theorem whc_cross_or_bottom_iff (a b : Site 2) (hab : (hypercubicLattice 2).Adj a b) :
    (whc_isCross whc_Htest a b ∨ s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1])) ↔
      sharedPrimalEdge a b ∈ (imageGraph jbc_Pce).edgeSet := by
  have hsy : sharedPrimalEdge a b = sharedPrimalEdge b a := sharedPrimalEdge_comm_of_adj hab
  unfold whc_isCross
  rw [whc_Htest_mem, whc_Htest_mem, ← hsy]
  constructor
  · intro h
    rcases h with h | h
    · rcases h with ⟨h, _⟩ | ⟨h, _⟩
      · exact h
      · exact h
    · exact (whc_shared_mem_square_iff a b hab).mpr (Or.inl h)
  · intro h
    by_cases hbot : s(a, b) = s(![(0:ℤ), 0], ![(0:ℤ), -1])
    · right; exact hbot
    · left; left
      exact ⟨h, fun hbadb => hbot ((whc_inv_bottom a b hab).mp hbadb)⟩


theorem whc_cutColoring_witness :
    whc_CutColoring whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1] whc_phiWitness := by
  intro a b hab
  have hadj := hab
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  rw [whc_cross_or_bottom_iff a b hab, whc_shared_mem_square_iff a b hab,
    whc_phiWitness_iff, whc_phiWitness_iff]
  rw [Sym2.eq_iff, Sym2.eq_iff, Sym2.eq_iff, Sym2.eq_iff]
  simp only [whc_site_eq_iff]
  set a0 := a 0; set a1 := a 1; set b0 := b 0; set b1 := b 1
  clear_value a0 a1 b0 b1
  clear hab
  have hd : (a0 = b0 ∧ (a1 = b1 + 1 ∨ b1 = a1 + 1)) ∨
      (a1 = b1 ∧ (a0 = b0 + 1 ∨ b0 = a0 + 1)) := by have := hadj; omega
  rcases hd with ⟨rfl, (rfl|rfl)⟩ | ⟨rfl, (rfl|rfl)⟩ <;> omega


theorem whc_Htest_adj_of_square (u v : Site 2) (h : (imageGraph jbc_Pce).Adj u v)
    (hne : s(u, v) ≠ s(![(0:ℤ), 0], ![1, 0])) : whc_Htest.Adj u v := by
  unfold whc_Htest
  rw [deleteEdges_adj, Set.mem_singleton_iff]
  exact ⟨h, hne⟩


theorem whc_Htest_reach_pq : whc_Htest.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] := by
  have sqAdj : ∀ u v : Site 2,
      s(u, v) ∈ (imageGraph jbc_Pce).edgeSet → (imageGraph jbc_Pce).Adj u v :=
    fun u v h => (SimpleGraph.mem_edgeSet _).mp h
  have e1 : whc_Htest.Adj ![(0:ℤ), 0] ![(0:ℤ), 1] :=
    whc_Htest_adj_of_square _ _
      (sqAdj _ _ (by rw [whc_square_mem_iff]; right; right; right; rw [Sym2.eq_iff]; tauto))
      (by rw [ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e2 : whc_Htest.Adj ![(0:ℤ), 1] ![(1:ℤ), 1] :=
    whc_Htest_adj_of_square _ _
      (sqAdj _ _ (by rw [whc_square_mem_iff]; right; right; left; rw [Sym2.eq_iff]; tauto))
      (by rw [ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  have e3 : whc_Htest.Adj ![(1:ℤ), 1] ![(1:ℤ), 0] :=
    whc_Htest_adj_of_square _ _
      (sqAdj _ _ (by rw [whc_square_mem_iff]; right; left; rw [Sym2.eq_iff]; tauto))
      (by rw [ne_eq, Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num)
  exact (e1.reachable.trans e2.reachable).trans e3.reachable


theorem whc_phiWitness_diff : ¬ (whc_phiWitness ![(0:ℤ), 0] ↔ whc_phiWitness ![(0:ℤ), -1]) := by
  rw [whc_phiWitness_iff, whc_phiWitness_iff]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num


theorem whc_residue_witness :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ whc_Htest.edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧
    (∃ φ : Site 2 → Prop, whc_CutColoring whc_Htest ![(0:ℤ), 0] ![(0:ℤ), -1] φ ∧
      (whc_Htest.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ↔ ¬ (φ ![(0:ℤ), 0] ↔ φ ![(0:ℤ), -1]))) := by
  refine ⟨?_, ?_, ?_, ?_, whc_phiWitness, whc_cutColoring_witness, ?_⟩
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rw [whc_Htest_mem]; push Not; intro _; rw [Sym2.eq_iff]; simp only [whc_site_eq_iff]; norm_num
  · rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  · rw [show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num
  · exact ⟨fun _ => whc_phiWitness_diff, fun _ => whc_Htest_reach_pq⟩


end Lattice
end StatMech
