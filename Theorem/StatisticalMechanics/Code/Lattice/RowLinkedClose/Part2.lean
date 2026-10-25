/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/RowLinkedClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitExteriorEven
import Theorem.StatisticalMechanics.Code.Lattice.JordanInteriorLib.Part4
import Def.StatisticalMechanics.Code.Lattice.RowLinkedClose
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem rlc_lexMeasure_lt {M : ℤ} {z z' : Site 2}
    (hz0 : -M < z 0) (hz0' : z 0 ≤ M) (hz1 : -M < z 1) (hz1' : z 1 ≤ M)
    (hz'0 : -M < z' 0) (hz'0' : z' 0 ≤ M) (hz'1 : -M < z' 1) (_hz'1' : z' 1 ≤ M)
    (hlex : z' 1 < z 1 ∨ (z' 1 = z 1 ∧ z' 0 < z 0)) :
    rlc_lexMeasure M z' < rlc_lexMeasure M z := by
  unfold rlc_lexMeasure
  set W : ℕ := (2 * M + 2).toNat with hW
  have hWpos : (z 0 + M).toNat < W := by omega
  have hWpos' : (z' 0 + M).toNat < W := by omega
  rcases hlex with h | ⟨h1, h0⟩
  · have hrow : (z' 1 + M).toNat < (z 1 + M).toNat := by omega
    calc (z' 1 + M).toNat * W + (z' 0 + M).toNat
        < (z' 1 + M).toNat * W + W := by omega
      _ = ((z' 1 + M).toNat + 1) * W := by ring
      _ ≤ (z 1 + M).toNat * W := Nat.mul_le_mul_right W hrow
      _ ≤ (z 1 + M).toNat * W + (z 0 + M).toNat := by omega
  · have hr : (z' 1 + M).toNat = (z 1 + M).toNat := by omega
    rw [hr]
    have : (z' 0 + M).toNat < (z 0 + M).toNat := by omega
    omega


theorem rlc_exists_lexMin_seed {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {z₀ : Site 2} (hz₀ : z₀ ∈ jil_offSupportInterior Vc) (M : ℤ) :
    ∃ seed ∈ jil_offSupportInterior Vc,
      ∀ z ∈ jil_offSupportInterior Vc,
        rlc_lexMeasure M seed ≤ rlc_lexMeasure M z := by
  classical
  have hfin := rlc_offSupportInterior_finite Vc
  have hne : (jil_offSupportInterior Vc).Nonempty := ⟨z₀, hz₀⟩
  obtain ⟨seed, hseed, hmin⟩ :=
    hfin.toFinset.exists_min_image (rlc_lexMeasure M)
      (by rw [Set.Finite.toFinset_nonempty]; exact hne)
  refine ⟨seed, (hfin.mem_toFinset).mp hseed, ?_⟩
  intro z hz
  exact hmin z (hfin.mem_toFinset.mpr hz)


theorem rlc_down_mem_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hdown : (![x, y - 1] : Site 2) ∉ Vc.support) :
    (![x, y - 1] : Site 2) ∈ jil_offSupportInterior Vc := by
  obtain ⟨hzsup, hzint⟩ := (jil_mem_offSupportInterior Vc _).mp hz
  have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x, y - 1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hpar := jec_localConstancy Vc hadj hzsup hdown
  rw [jil_mem_offSupportInterior]
  refine ⟨hdown, ?_⟩
  rw [jec_mem_leftRegion] at hzint ⊢
  intro h; exact hzint (hpar.mpr h)


theorem rlc_left_mem_interior {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) {x y : ℤ}
    (hz : (![x, y] : Site 2) ∈ jil_offSupportInterior Vc)
    (hleft : (![x - 1, y] : Site 2) ∉ Vc.support) :
    (![x - 1, y] : Site 2) ∈ jil_offSupportInterior Vc := by
  obtain ⟨hzsup, hzint⟩ := (jil_mem_offSupportInterior Vc _).mp hz
  have hadj : (hypercubicLattice 2).Adj (![x, y] : Site 2) ![x - 1, y] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have hpar := jec_localConstancy Vc hadj hzsup hleft
  rw [jil_mem_offSupportInterior]
  refine ⟨hleft, ?_⟩
  rw [jec_mem_leftRegion] at hzint ⊢
  intro h; exact hzint (hpar.mpr h)


end Lattice
end StatMech
