/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWContent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Def.StatisticalMechanics.Code.Universality.HexW2Cut.Part5
import Instance.StatisticalMechanics.Code.Universality.HexLiteralHWContent


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hhc_Dn_spec (a : ℂ) (h0 : ℤ) (N : ℕ) (d : hhc_Dn a h0 N) :
    (ofTurns a h0 d.1).IsLegalSAW ∧ d.1.length < N := by
  have h := (hzc_mem_truncFinset a h0 (N + 1) d.1).mp d.2
  refine ⟨h.1, ?_⟩
  simpa [numVertices] using h.2


theorem hhc_partial_eq (a : ℂ) (h0 : ℤ) (x : ℝ) (N : ℕ) :
    ∑ d : hhc_Dn a h0 N, x ^ d.1.length =
      ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n := by
  classical
  rw [show (∑ d : hhc_Dn a h0 N, x ^ d.1.length) =
      ∑ ts ∈ hzc_truncFinset a h0 (N + 1), x ^ ts.length from
        Finset.sum_coe_sort (hzc_truncFinset a h0 (N + 1)) (fun ts => x ^ ts.length)]
  rw [← Finset.sum_fiberwise_of_maps_to (t := Finset.range N)
      (g := List.length) ?_]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Finset.mem_range] at hn
    rw [Finset.sum_congr rfl (g := fun _ => x ^ n)
      (fun ts hts => by simp only [Finset.mem_filter] at hts; rw [hts.2])]
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard :
        ((hzc_truncFinset a h0 (N + 1)).filter (fun ts => ts.length = n)).card =
          hlc_sawCount a h0 n := by
      rw [← hlc_card_sawFinset a h0 n]
      congr 1
      ext ts
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨htr, hlen⟩
        rw [hlc_mem_sawFinset]
        exact ⟨(hzc_mem_truncFinset a h0 (N + 1) ts).mp htr |>.1, hlen⟩
      · intro hsaw
        have hs := (hlc_mem_sawFinset a h0 n ts).mp hsaw
        refine ⟨?_, hs.2⟩
        rw [hzc_mem_truncFinset]
        refine ⟨hs.1, ?_⟩
        simp [numVertices, hs.2]
        omega
    rw [hcard]
  · intro ts hts
    simp only [Finset.mem_range]
    have h := (hzc_mem_truncFinset a h0 (N + 1) ts).mp hts
    simpa [numVertices] using h.2


end StatMech.Universality
