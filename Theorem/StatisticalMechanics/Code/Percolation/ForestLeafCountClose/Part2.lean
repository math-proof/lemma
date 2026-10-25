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
import Def.StatisticalMechanics.Code.Percolation.ForestLeafCountClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem flc2_Tcount_le_boundary_of_spanningTree (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : flc2_SpanningTreeLeafCount ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  classical
  obtain ⟨W, _, _, G, _, ιT, lamL, hTree, hWcard, hdeg3, hιinj, hlammap, hlaminj⟩ := h
  
  set Tf := tfc_trifFinset ω n with hTf
  set Tw : Finset W := Tf.image ιT with hTw
  
  have hιinjOn : Set.InjOn ιT Tf := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx hy
    exact hιinj x hx.1 hx.2 y hy.1 hy.2 hxy
  have hcardTw : Tw.card = Tf.card := by
    rw [hTw, Finset.card_image_of_injOn hιinjOn]
  
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ G.degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨x, hxT, rfl⟩ := hw
    rw [tfc_mem_trifFinset] at hxT
    exact hdeg3 x hxT.1 hxT.2
  
  have h1 : Tf.card ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := by
    rw [← hcardTw]; exact flc2_trifImage_card_le_deg3 G Tw hTwdeg
  have h2 : (univ.filter (fun v => 3 ≤ G.degree v)).card
      < (univ.filter (fun v => G.degree v = 1)).card :=
    flc2_tree_internal_lt_leaves G hTree hWcard
  have h3 : (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard d n :=
    flc2_leaf_card_le_boundary G n lamL hlammap hlaminj
  calc Tcount d ω n = Tf.card := (tfc_trifFinset_card ω n).symm
    _ ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := h1
    _ ≤ (univ.filter (fun v => G.degree v = 1)).card := le_of_lt h2
    _ ≤ boxSV_boundaryCard d n := h3


theorem flc2_forest_component_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 1 ≤ G.degree v) (v : V) :
    ∃ w, G.Adj v w := by
  rw [← G.degree_pos_iff_exists_adj]; exact hmin v


theorem flc2_forest_internal_le_leaves {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card := by
  classical
  
  have hhand : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  
  
  have hEle : G.edgeFinset.card + 1 ≤ Fintype.card V := by
    
    obtain ⟨T, hGT, hTmax⟩ := exists_maximal_isAcyclic_of_le_isAcyclic (le_top (a := G)) hacyc
    
    have hmax2 : Maximal IsAcyclic T :=
      ⟨hTmax.1.2, fun H hHac hTH => hTmax.2 ⟨le_top, hHac⟩ hTH⟩
    have hTtree : T.IsTree := isTree_iff_maximal_isAcyclic.mpr ⟨‹Nonempty V›, hmax2⟩
    have hTedge : T.edgeFinset.card + 1 = Fintype.card V := hTtree.card_edgeFinset
    have hsub : G.edgeFinset ⊆ T.edgeFinset := by
      intro e he
      rw [SimpleGraph.mem_edgeFinset] at he ⊢
      exact SimpleGraph.edgeSet_subset_edgeSet.mpr hGT he
    have : G.edgeFinset.card ≤ T.edgeFinset.card := Finset.card_le_card hsub
    omega
  
  set indI : V → ℤ := fun v => if 3 ≤ G.degree v then 1 else 0 with hindI
  set indL : V → ℤ := fun v => if G.degree v = 1 then 1 else 0 with hindL
  have hbound : ∀ v, (2 : ℤ) + indI v - indL v ≤ (G.degree v : ℤ) := by
    intro v
    simp only [hindI, hindL]
    have h1 := hmin v
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
  
  have hRHS : ∑ v, (G.degree v : ℤ) ≤ 2 * Fintype.card V - 2 := by
    have h : (∑ v, (G.degree v : ℤ)) = ((∑ v, G.degree v : ℕ) : ℤ) := by rw [Nat.cast_sum]
    rw [h, hhand]
    have : (G.edgeFinset.card : ℤ) + 1 ≤ Fintype.card V := by exact_mod_cast hEle
    push_cast
    omega
  rw [hLHS] at hsumbound
  have hfin : ((univ.filter (fun v => 3 ≤ G.degree v)).card : ℤ)
      ≤ ((univ.filter (fun v => G.degree v = 1)).card : ℤ) := by linarith
  exact_mod_cast hfin


end Percolation
end StatMech
