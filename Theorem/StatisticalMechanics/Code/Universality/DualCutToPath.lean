/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/DualCutToPath.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem dcp_barrier_separates (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    {x y : Site 2} (hx : x ∈ leftSide 0 n 0 n) (hy : y ∈ rightSide 0 n 0 n) :
    ¬ (latticeMinusBarrier (bcd_leftReach ω n)).Reachable x y :=
  dcw_barrier_separates ω n hnoH hx hy


theorem dcp_topBarrierEdge_exists (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v w : Site 2, dcw_isBarrierEdge ω n v w ∧ v 1 = n ∧ w 1 = n := by
  classical
  
  have htl : (![0, n] : Site 2) ∈ bcd_leftReach ω n := by
    apply dcw_leftSide_in_L
    refine ⟨⟨by simp, by simpa using hn, by simpa using hn, by simp⟩, by simp⟩
  have htr : (![n, n] : Site 2) ∉ bcd_leftReach ω n := by
    apply dcw_rightSide_notin_L ω n hnoH
    refine ⟨⟨by simpa using hn, by simp, by simpa using hn, by simp⟩, by simp⟩
  
  set P : ℕ → Prop := fun k => (![(k:ℤ), n] : Site 2) ∈ bcd_leftReach ω n with hP
  have hP0 : P 0 := by simpa [hP] using htl
  have hPn : ¬ P n.toNat := by
    have : ((n.toNat : ℤ)) = n := by omega
    simpa [hP, this] using htr
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
  refine ⟨![((k:ℤ) - 1), n], ![(k:ℤ), n], ?_, by simp, by simp⟩
  have hv : (![((k:ℤ) - 1), n] : Site 2) ∈ bcd_leftReach ω n := by
    have hcast : ((k - 1 : ℕ) : ℤ) = (k:ℤ) - 1 := by omega
    rw [hP] at hkprev; rwa [hcast] at hkprev
  refine ⟨hv, ?_, ?_, ?_⟩
  · 
    have hvbox : (![((k:ℤ) - 1), n] : Site 2) ∈ rect 0 n 0 n := hv.1
    rw [mem_rect] at hvbox ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hvbox ⊢
    refine ⟨by omega, ?_, hn, le_refl n⟩
    have hkle : k ≤ n.toNat := Nat.find_le hPn
    omega
  · simpa [hP] using hkfail
  · 
    rw [hypercubicLattice_adj, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    omega


theorem dcp_dualBarrierGraph_support (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {p q : Site 2} (h : (dcw_dualBarrierGraph ω n).Adj p q) :
    p ∈ rot90Fun '' (rect 0 n 0 n) ∧ q ∈ rot90Fun '' (rect 0 n 0 n) := by
  obtain ⟨v, w, hvw, hpq⟩ := h
  have hvbox : v ∈ rect 0 n 0 n := hvw.1.1
  have hwbox : w ∈ rect 0 n 0 n := hvw.2.1
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · exact ⟨⟨v, hvbox, hp.symm⟩, ⟨w, hwbox, hq.symm⟩⟩
  · exact ⟨⟨w, hwbox, hp.symm⟩, ⟨v, hvbox, hq.symm⟩⟩


theorem dcp_dualBarrierGraph_finite_support (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    {p : Site 2 | ∃ q, (dcw_dualBarrierGraph ω n).Adj p q}.Finite := by
  apply Set.Finite.subset ((rect_finite 0 n 0 n).image rot90Fun)
  rintro p ⟨q, hpq⟩
  exact (dcp_dualBarrierGraph_support ω n hpq).1


end Universality
end StatMech
