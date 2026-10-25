/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCircuitToWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Def.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem dcw_dualVerticalCrossing_of_route (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hroute : dcw_BarrierRoute ω n) :
    DualVerticalCrossing ω 0 n 0 n := by
  obtain ⟨p₀, hp₀, q₀, hq₀, c, hsupp⟩ := hroute
  
  set c' : (openSubgraph 2 (dualConfig ω)).Walk p₀ q₀ := dcw_dualBarrier_walk_open ω n c with hc'
  
  have hsupp' : c'.support = c.support := by
    rw [hc', dcw_dualBarrier_walk_open, SimpleGraph.Walk.support_mapLe_eq_support]
  have hsuppbox : ∀ u ∈ c'.support, u ∈ rect 0 n 0 n := by
    intro u hu; rw [hsupp'] at hu; exact hsupp u hu
  
  refine ⟨⟨p₀, hp₀⟩, ⟨q₀, hq₀⟩, ?_⟩
  
  exact walk_induce_reachable (openSubgraph 2 (dualConfig ω)) (rect 0 n 0 n) c'
    hsuppbox (bottomSide_subset hp₀) (topSide_subset hq₀)


theorem dcw_dualVertical_of_no_horizontal (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hroute : dcw_BarrierRoute ω n) :
    DualVerticalCrossing ω 0 n 0 n :=
  dcw_dualVerticalCrossing_of_route ω n hroute


theorem dcw_square_dichotomy (n : ℤ)
    (hroute : ∀ ω : ConfigSpace (Sym2 (Site 2)),
      ¬ HorizontalCrossing ω 0 n 0 n → dcw_BarrierRoute ω n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n := by
  intro ω hω
  rw [Set.mem_compl_iff, mem_horizontalCrossingEvent] at hω
  rw [mem_dualVerticalCrossingEvent]
  exact dcw_dualVertical_of_no_horizontal ω n (hroute ω hω)


theorem dcw_dualBarrier_isOpenDual (n : ℤ)
    (hroute : ∀ ω : ConfigSpace (Sym2 (Site 2)),
      ¬ HorizontalCrossing ω 0 n 0 n → dcw_BarrierRoute ω n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ dualVerticalCrossingEvent 0 n 0 n :=
  dcw_square_dichotomy n hroute


theorem dcw_barrierEdge_exists (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧ v 1 = 0 ∧ w 1 = 0 := by
  classical
  
  have hbl : (![0, 0] : Site 2) ∈ bcd_leftReach ω n := by
    apply dcw_leftSide_in_L
    refine ⟨⟨by simp, by simpa using hn, by simp, by simpa using hn⟩, by simp⟩
  have hbr : (![n, 0] : Site 2) ∉ bcd_leftReach ω n := by
    apply dcw_rightSide_notin_L ω n hnoH
    refine ⟨⟨by simpa using hn, by simp, by simp, by simpa using hn⟩, by simp⟩
  
  set P : ℕ → Prop := fun k => (![(k:ℤ), 0] : Site 2) ∈ bcd_leftReach ω n with hP
  have hP0 : P 0 := by simpa [hP] using hbl
  have hPn : ¬ P n.toNat := by
    have : ((n.toNat : ℤ)) = n := by omega
    simpa [hP, this] using hbr
  
  have hex : ∃ k, ¬ P k := ⟨n.toNat, hPn⟩
  set k := Nat.find hex with hk
  have hkfail : ¬ P k := Nat.find_spec hex
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0] at hkfail; exact absurd hP0 hkfail
    · exact h0
  
  have hkprev : P (k - 1) := by
    by_contra hcon
    have : k ≤ k - 1 := Nat.find_le hcon
    omega
  
  refine ⟨![((k:ℤ) - 1), 0], ![(k:ℤ), 0], ?_, by simp, by simp⟩
  have hv : (![((k:ℤ) - 1), 0] : Site 2) ∈ bcd_leftReach ω n := by
    have hcast : ((k - 1 : ℕ) : ℤ) = (k:ℤ) - 1 := by omega
    rw [hP] at hkprev; rwa [hcast] at hkprev
  refine ⟨hv, ?_, ?_, ?_⟩
  · 
    have hvbox : (![((k:ℤ) - 1), 0] : Site 2) ∈ rect 0 n 0 n := hv.1
    rw [mem_rect] at hvbox ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hvbox ⊢
    refine ⟨by omega, ?_, le_refl 0, hn⟩
    
    have hkle : k ≤ n.toNat := Nat.find_le hPn
    omega
  · 
    simpa [hP] using hkfail
  · 
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega


theorem dcw_dualBarrierGraph_nonempty_edge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ p q : Site 2, (dcw_dualBarrierGraph ω n).Adj p q := by
  obtain ⟨v, w, hbar, _, _⟩ := dcw_barrierEdge_exists ω n hn hnoH
  exact ⟨rot90Fun v, rot90Fun w, v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩

end Universality
end StatMech
