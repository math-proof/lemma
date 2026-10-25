/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexZConvClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexZConvClose.Part3


namespace StatMech.Universality

open scoped BigOperators

open HexWalk


theorem hzc_filterCard_eq (a : ℂ) (h0 : ℤ) (N n : ℕ) (hn : n < N) :
    ((hzc_truncFinset a h0 N).filter
        (fun ts => (ofTurns a h0 ts).numVertices = n)).card = hzc_sawCount a h0 n := by
  classical
  unfold hzc_sawCount
  congr 1
  ext ts
  simp only [Finset.mem_filter, hzc_mem_truncFinset]
  constructor
  · rintro ⟨⟨hleg, _⟩, hv⟩; exact ⟨⟨hleg, by omega⟩, hv⟩
  · rintro ⟨⟨hleg, _⟩, hv⟩; exact ⟨⟨hleg, by omega⟩, hv⟩


theorem hzc_sawCount_zero (a : ℂ) (h0 : ℤ) : hzc_sawCount a h0 0 = 0 := by
  classical
  unfold hzc_sawCount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro ts _
  have : (ofTurns a h0 ts).numVertices = ts.length + 1 := by rw [numVertices_eq]; rfl
  omega


theorem hzc_trunc_wt (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) {ts : List ℤ}
    (h : ts ∈ hzc_truncFinset a h0 N) :
    hexSAWwt a h0 x ts = x ^ (ofTurns a h0 ts).numVertices :=
  hexSAWwt_of_isLegalSAW a h0 x ((hzc_mem_truncFinset a h0 N ts).mp h).1


theorem hzc_partial_eq (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ ts ∈ hzc_truncFinset a h0 N, hexSAWwt a h0 x ts
      = ∑ n ∈ Finset.range N, (hzc_sawCount a h0 n : ℝ) * x ^ n := by
  classical
  rw [Finset.sum_congr rfl (fun ts h => hzc_trunc_wt a h0 x N h)]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range N)
        (g := fun ts => (ofTurns a h0 ts).numVertices) ?_]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range] at hn
    rw [Finset.sum_congr rfl (g := fun _ => x ^ n)
          (fun ts hts => by simp only [Finset.mem_filter] at hts; rw [hts.2])]
    rw [Finset.sum_const, nsmul_eq_mul, hzc_filterCard_eq a h0 N n hn]
  · intro ts hts
    simp only [Finset.mem_range]
    exact ((hzc_mem_truncFinset a h0 N ts).mp hts).2


end StatMech.Universality
