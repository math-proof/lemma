/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ForestLeafCountClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem flc2_deg_pos_of_connected {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hV : 2 ≤ Fintype.card V) (v : V) :
    1 ≤ G.degree v := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hV v
  have hr : G.Reachable v w := hconn.preconnected v w
  have hex : ∃ u, G.Adj v u := by
    obtain ⟨p⟩ := hr
    cases p with
    | nil => exact absurd rfl (Ne.symm hw)
    | cons hadj _ => exact ⟨_, hadj⟩
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, G.degree_pos_iff_exists_adj]
  exact hex


theorem flc2_tree_internal_lt_leaves {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : G.IsTree) (hV : 2 ≤ Fintype.card V) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      < (univ.filter (fun v => G.degree v = 1)).card := by
  classical
  have hpos := flc2_deg_pos_of_connected G hT.connected hV
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


theorem flc2_trifImage_card_le_deg3 {W : Type*} [Fintype W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (Tw : Finset W) (hTw : ∀ w ∈ Tw, 3 ≤ G.degree w) :
    Tw.card ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := by
  classical
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hTw w hw


theorem flc2_leaf_card_le_boundary {W : Type*} [Fintype W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (n : ℕ) (lam : W → Site d)
    (hmap : ∀ v, G.degree v = 1 → lam v ∈ vertexBoundary d n)
    (hinj : Set.InjOn lam (univ.filter (fun v => G.degree v = 1))) :
    (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard d n := by
  classical
  rw [← tfc_boundaryFinset_card]
  apply Finset.card_le_card_of_injOn lam
  · intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    rw [Finset.mem_coe, tfc_mem_boundaryFinset]
    exact hmap v hv.2
  · exact hinj


end Percolation
end StatMech
