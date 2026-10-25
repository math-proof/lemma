/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafDisjointClose.Part2
import Def.StatisticalMechanics.Code.Percolation.OutwardArmForestClose.Part5
open Set SimpleGraph Finset
open scoped BigOperators

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


namespace OafTree

theorem oaf_sub_const_on_cut : ∀ a b, (oaf_cutGraph G 0).Adj a b → sub a = sub b := by decide


theorem oaf_children_separated (i j : Fin 3) (hij : i ≠ j) :
    ¬ (oaf_cutGraph G 0).Reachable (child i) (child j) := by
  intro h
  have hlab := oaf_reach_eqLabel (oaf_cutGraph G 0) sub oaf_sub_const_on_cut h
  fin_cases i <;> fin_cases j <;> simp_all [child, sub]


theorem oaf_adj_reach {a b : V} (h : G.Adj a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    (oaf_cutGraph G 0).Reachable a b :=
  SimpleGraph.Adj.reachable (G := oaf_cutGraph G 0) ⟨h, ha, hb⟩


theorem oaf_cover_leaf (a : V) (haT : a ∉ Ttree) :
    (oaf_cutGraph G 0).Reachable a (child (sub a)) := by
  fin_cases a <;>
    first
      
      | exact absurd (by decide : (_ : V) ∈ Ttree) haT
      
      | exact oaf_adj_reach (by unfold G fromRel E edges; decide) (by decide) (by decide)


theorem oaf_edge_reach {a b : V} (h : G.Adj a b) : G.Reachable a b :=
  SimpleGraph.Adj.reachable h

theorem oaf_adj01 : G.Adj 0 1 := by unfold G fromRel E edges; decide

theorem oaf_adj02 : G.Adj 0 2 := by unfold G fromRel E edges; decide

theorem oaf_adj03 : G.Adj 0 3 := by unfold G fromRel E edges; decide


theorem oaf_root_reach (a : V) : G.Reachable 0 a := by
  fin_cases a
  · exact Reachable.refl _
  · exact oaf_edge_reach oaf_adj01
  · exact oaf_edge_reach oaf_adj02
  · exact oaf_edge_reach oaf_adj03
  · exact (oaf_edge_reach oaf_adj01).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))
  · exact (oaf_edge_reach oaf_adj01).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))
  · exact (oaf_edge_reach oaf_adj02).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))
  · exact (oaf_edge_reach oaf_adj02).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))
  · exact (oaf_edge_reach oaf_adj03).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))
  · exact (oaf_edge_reach oaf_adj03).trans
      (oaf_edge_reach (by unfold G fromRel E edges; decide))


theorem oaf_tree_not_forestPeel : ¬ oaf_AbstractForestPeel G Ttree := by
  refine oaf_abstractForestPeel_false_of_rootCover G Ttree (r := 0) (c := child) ?_ ?_ ?_ ?_
  · decide
  · intro i; fin_cases i <;> decide
  · intro i; fin_cases i <;> decide
  · intro a _ haT
    exact ⟨sub a, oaf_cover_leaf a haT⟩


theorem oaf_root_deg : 3 ≤ G.degree 0 := by decide


theorem oaf_child_deg : ∀ i : Fin 3, 3 ≤ G.degree (child i) := by decide

end OafTree


theorem oaf_deg_pos_of_connected {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hconn : G.Connected) (hV : 2 ≤ Fintype.card V) (v : V) : 1 ≤ G.degree v := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hV v
  have hr : G.Reachable v w := hconn.preconnected v w
  have hex : ∃ u, G.Adj v u := by
    obtain ⟨p⟩ := hr
    cases p with
    | nil => exact absurd rfl (Ne.symm hw)
    | cons hadj _ => exact ⟨_, hadj⟩
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, G.degree_pos_iff_exists_adj]
  exact hex


theorem oaf_tree_internal_lt_leaves {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : G.IsTree) (hV : 2 ≤ Fintype.card V) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      < (univ.filter (fun v => G.degree v = 1)).card := by
  classical
  have hpos := oaf_deg_pos_of_connected G hT.connected hV
  have hhand : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hedge : G.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  set indI : V → ℤ := fun v => if 3 ≤ G.degree v then 1 else 0 with hindI
  set indL : V → ℤ := fun v => if G.degree v = 1 then 1 else 0 with hindL
  
  have hbound : ∀ v, (2 : ℤ) + indI v - indL v ≤ (G.degree v : ℤ) := by
    intro v
    simp only [hindI, hindL]
    have h1 := hpos v
    have hcast : (1 : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast h1
    by_cases h3 : 3 ≤ G.degree v
    · have hne1 : ¬ G.degree v = 1 := by omega
      have h3cast : (3 : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast h3
      simp only [if_pos h3, if_neg hne1]; linarith
    · by_cases h1' : G.degree v = 1
      · have h1cast : (G.degree v : ℤ) = 1 := by exact_mod_cast h1'
        simp only [if_neg h3, if_pos h1']; linarith
      · have h2 : G.degree v = 2 := by omega
        have h2cast : (G.degree v : ℤ) = 2 := by exact_mod_cast h2
        simp only [if_neg h3, if_neg h1']; linarith
  have hsumbound : ∑ v, ((2 : ℤ) + indI v - indL v) ≤ ∑ v, (G.degree v : ℤ) :=
    Finset.sum_le_sum (fun v _ => hbound v)
  
  have hLHS : ∑ v, ((2 : ℤ) + indI v - indL v)
      = 2 * Fintype.card V + (univ.filter (fun v => 3 ≤ G.degree v)).card
        - (univ.filter (fun v => G.degree v = 1)).card := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [hindI, hindL, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_boole, Finset.sum_boole]
    ring
  
  have hRHS : ∑ v, (G.degree v : ℤ) = 2 * Fintype.card V - 2 := by
    have h : (∑ v, (G.degree v : ℤ)) = ((∑ v, G.degree v : ℕ) : ℤ) := by
      rw [Nat.cast_sum]
    rw [h, hhand]; omega
  rw [hLHS, hRHS] at hsumbound
  
  have hfin : ((univ.filter (fun v => 3 ≤ G.degree v)).card : ℤ)
      < ((univ.filter (fun v => G.degree v = 1)).card : ℤ) := by linarith
  exact_mod_cast hfin

end Percolation
end StatMech
