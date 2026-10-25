/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanIsCyclesCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanEulerInduction.Part3
import Theorem.StatisticalMechanics.Code.Lattice.WhitneyBridge.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenClose.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanEvenBiconditional.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanFaithfulCount.Part6
import Theorem.StatisticalMechanics.Code.Lattice.JordanVeblenStep
open SimpleGraph Set


namespace StatMech

namespace Lattice

theorem jic_edge_at_q_not_mem (G : SimpleGraph (Site 2)) {q : Site 2}
    (hfree : ∀ w, ¬ G.Adj q w) {u v : Site 2} (hq : u = q ∨ v = q) :
    s(u, v) ∉ G.edgeSet := by
  rw [SimpleGraph.mem_edgeSet]
  intro hG
  rcases hq with rfl | rfl
  · exact hfree v hG
  · exact hfree u hG.symm


theorem jic_adj_NE_NW (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a - 1, b] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

theorem jic_adj_NW_SW (a b : ℤ) : (hypercubicLattice 2).Adj ![a - 1, b] ![a - 1, b - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

theorem jic_adj_SW_SE (a b : ℤ) : (hypercubicLattice 2).Adj ![a - 1, b - 1] ![a, b - 1] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp

theorem jic_adj_SE_NE (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b - 1] ![a, b] := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp


theorem jic_shared_NE_NW (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a - 1, b] = s(![a, b], ![a, b + 1]) := by
  rw [sharedPrimalEdge_left]; unfold faceCorner00 faceCorner01; rfl

theorem jic_shared_NW_SW (a b : ℤ) :
    sharedPrimalEdge ![a - 1, b] ![a - 1, b - 1] = s(![a - 1, b], ![a, b]) := by
  unfold sharedPrimalEdge
  rw [if_pos (by simp only [Matrix.cons_val_zero])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max b (b - 1) = b by omega]
  rw [Sym2.eq_iff]; left; constructor <;> (funext i; fin_cases i <;> simp <;> try omega)

theorem jic_shared_SW_SE (a b : ℤ) :
    sharedPrimalEdge ![a - 1, b - 1] ![a, b - 1] = s(![a, b - 1], ![a, b]) := by
  unfold sharedPrimalEdge
  rw [if_neg (by simp only [Matrix.cons_val_zero]; omega)]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max (a - 1) a = a by omega]
  rw [Sym2.eq_iff]; left; constructor <;> (funext i; fin_cases i <;> simp <;> try omega)

theorem jic_shared_SE_NE (a b : ℤ) :
    sharedPrimalEdge ![a, b - 1] ![a, b] = s(![a, b], ![a + 1, b]) := by
  unfold sharedPrimalEdge
  rw [if_pos (by simp only [Matrix.cons_val_zero])]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show max (b - 1) b = b by omega]


theorem jic_faces_distinct (a b : ℤ) :
    (![a, b] : Site 2) ≠ ![a - 1, b] ∧ (![a, b] : Site 2) ≠ ![a - 1, b - 1] ∧
      (![a, b] : Site 2) ≠ ![a, b - 1] ∧ (![a - 1, b] : Site 2) ≠ ![a - 1, b - 1] ∧
      (![a - 1, b] : Site 2) ≠ ![a, b - 1] ∧ (![a - 1, b - 1] : Site 2) ≠ ![a, b - 1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro h; have h0 := congrFun h 0; have h1 := congrFun h 1;
     simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1; omega)


theorem jic_pres_NE_NW (G : SimpleGraph (Site 2)) (a b : ℤ)
    (hfree : ∀ w, ¬ G.Adj ![a, b] w) : (whb_faceRegion G).Adj ![a, b] ![a - 1, b] := by
  refine ⟨jic_adj_NE_NW a b, ?_⟩
  rw [jic_shared_NE_NW]; exact jic_edge_at_q_not_mem G hfree (Or.inl rfl)

theorem jic_pres_NW_SW (G : SimpleGraph (Site 2)) (a b : ℤ)
    (hfree : ∀ w, ¬ G.Adj ![a, b] w) : (whb_faceRegion G).Adj ![a - 1, b] ![a - 1, b - 1] := by
  refine ⟨jic_adj_NW_SW a b, ?_⟩
  rw [jic_shared_NW_SW]; exact jic_edge_at_q_not_mem G hfree (Or.inr rfl)

theorem jic_pres_SW_SE (G : SimpleGraph (Site 2)) (a b : ℤ)
    (hfree : ∀ w, ¬ G.Adj ![a, b] w) : (whb_faceRegion G).Adj ![a - 1, b - 1] ![a, b - 1] := by
  refine ⟨jic_adj_SW_SE a b, ?_⟩
  rw [jic_shared_SW_SE]; exact jic_edge_at_q_not_mem G hfree (Or.inr rfl)

theorem jic_pres_SE_NE (G : SimpleGraph (Site 2)) (a b : ℤ)
    (hfree : ∀ w, ¬ G.Adj ![a, b] w) : (whb_faceRegion G).Adj ![a, b - 1] ![a, b] := by
  refine ⟨jic_adj_SE_NE a b, ?_⟩
  rw [jic_shared_SE_NE]; exact jic_edge_at_q_not_mem G hfree (Or.inl rfl)


theorem jic_surv_reachable (G : SimpleGraph (Site 2)) (e : Sym2 (Site 2)) {u v : Site 2}
    (hadj : (whb_faceRegion G).Adj u v) (hne : s(u, v) ≠ e) :
    ((whb_faceRegion G).deleteEdges {e}).Reachable u v :=
  (SimpleGraph.deleteEdges_adj.mpr ⟨hadj, by rw [Set.mem_singleton_iff]; exact hne⟩).reachable


theorem jic_quad_edge_ne {u₁ v₁ u₂ v₂ : Site 2}
    (h : ¬ ((u₁ = u₂ ∧ v₁ = v₂) ∨ (u₁ = v₂ ∧ v₁ = u₂))) : s(u₁, v₁) ≠ s(u₂, v₂) := by
  rw [ne_eq, Sym2.eq_iff]; exact h


theorem jic_dangling_east (G : SimpleGraph (Site 2)) (a b : ℤ) (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
    ((whb_faceRegion G).deleteEdges {s((![a, b] : Site 2), ![a, b - 1])}).Reachable
      ![a, b] ![a, b - 1] := by
  have ne1 : s((![a, b] : Site 2), ![a - 1, b]) ≠ s((![a, b] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne2 : s((![a - 1, b] : Site 2), ![a - 1, b - 1]) ≠ s((![a, b] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne3 : s((![a - 1, b - 1] : Site 2), ![a, b - 1]) ≠ s((![a, b] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have r1 := jic_surv_reachable G _ (jic_pres_NE_NW G a b hfree) ne1
  have r2 := jic_surv_reachable G _ (jic_pres_NW_SW G a b hfree) ne2
  have r3 := jic_surv_reachable G _ (jic_pres_SW_SE G a b hfree) ne3
  exact (r1.trans r2).trans r3


theorem jic_dangling_north (G : SimpleGraph (Site 2)) (a b : ℤ) (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
    ((whb_faceRegion G).deleteEdges {s((![a, b] : Site 2), ![a - 1, b])}).Reachable
      ![a, b] ![a - 1, b] := by
  have ne1 : s((![a, b - 1] : Site 2), ![a, b]) ≠ s((![a, b] : Site 2), ![a - 1, b]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne2 : s((![a - 1, b - 1] : Site 2), ![a, b - 1]) ≠ s((![a, b] : Site 2), ![a - 1, b]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne3 : s((![a - 1, b] : Site 2), ![a - 1, b - 1]) ≠ s((![a, b] : Site 2), ![a - 1, b]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have r1 := jic_surv_reachable G _ (jic_pres_SE_NE G a b hfree) ne1
  have r2 := jic_surv_reachable G _ (jic_pres_SW_SE G a b hfree) ne2
  have r3 := jic_surv_reachable G _ (jic_pres_NW_SW G a b hfree) ne3
  
  exact ((r1.symm.trans r2.symm).trans r3.symm)


theorem jic_dangling_west (G : SimpleGraph (Site 2)) (a b : ℤ) (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
    ((whb_faceRegion G).deleteEdges {s((![a - 1, b] : Site 2), ![a - 1, b - 1])}).Reachable
      ![a - 1, b] ![a - 1, b - 1] := by
  have ne1 : s((![a, b] : Site 2), ![a - 1, b]) ≠ s((![a - 1, b] : Site 2), ![a - 1, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne2 : s((![a, b - 1] : Site 2), ![a, b]) ≠ s((![a - 1, b] : Site 2), ![a - 1, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne3 : s((![a - 1, b - 1] : Site 2), ![a, b - 1]) ≠ s((![a - 1, b] : Site 2), ![a - 1, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have r1 := jic_surv_reachable G _ (jic_pres_NE_NW G a b hfree) ne1
  have r2 := jic_surv_reachable G _ (jic_pres_SE_NE G a b hfree) ne2
  have r3 := jic_surv_reachable G _ (jic_pres_SW_SE G a b hfree) ne3
  
  exact ((r1.symm.trans r2.symm).trans r3.symm)


theorem jic_dangling_south (G : SimpleGraph (Site 2)) (a b : ℤ) (hfree : ∀ w, ¬ G.Adj ![a, b] w) :
    ((whb_faceRegion G).deleteEdges {s((![a - 1, b - 1] : Site 2), ![a, b - 1])}).Reachable
      ![a - 1, b - 1] ![a, b - 1] := by
  have ne1 : s((![a - 1, b] : Site 2), ![a - 1, b - 1]) ≠ s((![a - 1, b - 1] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne2 : s((![a, b] : Site 2), ![a - 1, b]) ≠ s((![a - 1, b - 1] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have ne3 : s((![a, b - 1] : Site 2), ![a, b]) ≠ s((![a - 1, b - 1] : Site 2), ![a, b - 1]) :=
    jic_quad_edge_ne (by rintro (⟨ha, hb⟩ | ⟨ha, hb⟩) <;>
      (have a0 := congrFun ha 0; have a1 := congrFun ha 1; have b0 := congrFun hb 0;
       have b1 := congrFun hb 1;
       simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at a0 a1 b0 b1; omega))
  have r1 := jic_surv_reachable G _ (jic_pres_NW_SW G a b hfree) ne1
  have r2 := jic_surv_reachable G _ (jic_pres_NE_NW G a b hfree) ne2
  have r3 := jic_surv_reachable G _ (jic_pres_SE_NE G a b hfree) ne3
  
  exact ((r1.symm.trans r2.symm).trans r3.symm)


theorem jic_dangling_bridge (G : SimpleGraph (Site 2)) {p q : Site 2}
    (hfree : ∀ w, ¬ G.Adj q w) (hpq : (hypercubicLattice 2).Adj p q) :
    ∃ f0 g0 : Site 2, (hypercubicLattice 2).Adj f0 g0 ∧
      sharedPrimalEdge f0 g0 = s(p, q) ∧
      ((whb_faceRegion G).deleteEdges {s(f0, g0)}).Reachable f0 g0 := by
  obtain ⟨a, b, hqf⟩ : ∃ a b : ℤ, q = ![a, b] := ⟨q 0, q 1, by funext i; fin_cases i <;> rfl⟩
  subst hqf
  have hpq' := hpq
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hpq'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hpq'
  have hcase : (p = ![a + 1, b]) ∨ (p = ![a - 1, b]) ∨ (p = ![a, b + 1]) ∨ (p = ![a, b - 1]) := by
    have hh : (p 0 = a ∧ (p 1 = b + 1 ∨ p 1 = b - 1)) ∨
        (p 1 = b ∧ (p 0 = a + 1 ∨ p 0 = a - 1)) := by omega
    rcases hh with ⟨h0, (h1 | h1)⟩ | ⟨h1, (h0 | h0)⟩
    · exact Or.inr (Or.inr (Or.inl (by rw [jeb_site_eq_iff]; omega)))
    · exact Or.inr (Or.inr (Or.inr (by rw [jeb_site_eq_iff]; omega)))
    · exact Or.inl (by rw [jeb_site_eq_iff]; omega)
    · exact Or.inr (Or.inl (by rw [jeb_site_eq_iff]; omega))
  rcases hcase with rfl | rfl | rfl | rfl
  · 
    refine ⟨![a, b], ![a, b - 1], (jic_adj_SE_NE a b).symm, ?_, jic_dangling_east G a b hfree⟩
    rw [sharedPrimalEdge_comm_of_adj (jic_adj_SE_NE a b).symm, jic_shared_SE_NE, Sym2.eq_swap]
  · 
    refine ⟨![a - 1, b], ![a - 1, b - 1], jic_adj_NW_SW a b, ?_, jic_dangling_west G a b hfree⟩
    rw [jic_shared_NW_SW]
  · 
    refine ⟨![a, b], ![a - 1, b], jic_adj_NE_NW a b, ?_, jic_dangling_north G a b hfree⟩
    rw [jic_shared_NE_NW, Sym2.eq_swap]
  · 
    refine ⟨![a - 1, b - 1], ![a, b - 1], jic_adj_SW_SE a b, ?_, jic_dangling_south G a b hfree⟩
    rw [jic_shared_SW_SE, Sym2.eq_swap]


theorem jic_pushGraph_sup (P : PlanarZ2Subgraph) (A B : SimpleGraph P.V) :
    jei_pushGraph P (A ⊔ B) = jei_pushGraph P A ⊔ jei_pushGraph P B := by
  ext a b
  simp only [jei_pushGraph_adj, sup_adj]
  constructor
  · rintro ⟨x, y, (h | h), hx, hy⟩
    · exact Or.inl ⟨x, y, h, hx, hy⟩
    · exact Or.inr ⟨x, y, h, hx, hy⟩
  · rintro (⟨x, y, h, hx, hy⟩ | ⟨x, y, h, hx, hy⟩)
    · exact ⟨x, y, Or.inl h, hx, hy⟩
    · exact ⟨x, y, Or.inr h, hx, hy⟩


end Lattice
end StatMech
