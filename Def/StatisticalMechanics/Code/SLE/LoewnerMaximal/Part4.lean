/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerMaximal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.LoewnerExistence
import Theorem.StatisticalMechanics.Code.SLE.LoewnerMaximal.Part4
open Complex Set Metric Filter Topology
open scoped ENNReal NNReal ComplexConjugate


namespace StatMech.SLE

noncomputable def LoewnerForwardSolution.appendCurve
    {W : ℝ → ℝ} {z : ℂ} {S T : ℝ}
    (g : LoewnerForwardSolution W z S)
    (h : LoewnerForwardSolution (fun u ↦ W (S + u)) (g.curve S) T) :
    ℝ → ℂ := fun t ↦ if t ≤ S then g.curve t else h.curve (t - S)


noncomputable def LoewnerForwardSolution.append
    {W : ℝ → ℝ} {z : ℂ} {S T : ℝ}
    (g : LoewnerForwardSolution W z S)
    (h : LoewnerForwardSolution (fun u ↦ W (S + u)) (g.curve S) T)
    (hS : 0 ≤ S) (hT : 0 ≤ T) :
    LoewnerForwardSolution W z (S + T) where
  curve := g.appendCurve h
  initial := by simp [LoewnerForwardSolution.appendCurve, hS, g.initial]
  deriv := by
    intro t ht
    by_cases hleft : t < S
    · have htS : t ∈ Icc (0 : ℝ) S := ⟨ht.1, hleft.le⟩
      have hlocal : Icc (0 : ℝ) S ∈ 𝓝[Icc (0 : ℝ) (S + T)] t := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hleft)] with x hx hxs
        exact ⟨hx.1, hxs⟩
      have hd := (g.deriv t htS).mono_of_mem_nhdsWithin hlocal
      have happ : (g.appendCurve h) t = g.curve t := by
        simp [LoewnerForwardSolution.appendCurve, hleft.le]
      rw [happ]
      apply hd.congr_of_eventuallyEq_of_mem _ ht
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hleft)] with x hx
      change x ≤ S at hx
      simp [LoewnerForwardSolution.appendCurve, hx]
    · by_cases hright : S < t
      · have hsub : t - S ∈ Icc (0 : ℝ) T := ⟨by linarith, by linarith [ht.2]⟩
        let k : ℝ → ℂ := fun x ↦ h.curve (x - S)
        have hmap : MapsTo (fun x : ℝ ↦ x - S) (Icc S (S + T)) (Icc 0 T) := by
          intro x hx
          change 0 ≤ x - S ∧ x - S ≤ T
          constructor <;> linarith [hx.1, hx.2]
        have hinner : HasDerivWithinAt (fun x : ℝ ↦ x - S) 1
            (Icc S (S + T)) t := by
          simpa using ((hasDerivAt_id t).sub_const S).hasDerivWithinAt
        have hk : HasDerivWithinAt k
            (loewnerField W t (k t)) (Icc S (S + T)) t := by
          have hraw := (h.deriv (t - S) hsub).scomp t hinner hmap
          convert hraw using 1
          simp only [one_smul]
          change loewnerField W t (h.curve (t - S)) =
            loewnerField W (S + (t - S)) (h.curve (t - S))
          rw [show S + (t - S) = t by ring]
        have hlocal : Icc S (S + T) ∈ 𝓝[Icc (0 : ℝ) (S + T)] t := by
          filter_upwards [self_mem_nhdsWithin,
            mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hright)] with x hx hxs
          exact ⟨hxs, hx.2⟩
        have hk' := hk.mono_of_mem_nhdsWithin hlocal
        have happ : (g.appendCurve h) t = k t := by
          simp [LoewnerForwardSolution.appendCurve, k, not_le.mpr hright]
        rw [happ]
        apply hk'.congr_of_eventuallyEq_of_mem _ ht
        filter_upwards [mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hright)] with x hx
        change S ≤ x at hx
        rcases hx.eq_or_lt with rfl | hxlt
        · simp [LoewnerForwardSolution.appendCurve, k, h.initial]
        · simp [LoewnerForwardSolution.appendCurve, k, not_le.mpr hxlt]
      · have hts : t = S := le_antisymm (not_lt.mp hright) (not_lt.mp hleft)
        subst t
        let k : ℝ → ℂ := fun x ↦ h.curve (x - S)
        have hmap : MapsTo (fun x : ℝ ↦ x - S) (Icc S (S + T)) (Icc 0 T) := by
          intro x hx
          change 0 ≤ x - S ∧ x - S ≤ T
          constructor <;> linarith [hx.1, hx.2]
        have hinner : HasDerivWithinAt (fun x : ℝ ↦ x - S) 1
            (Icc S (S + T)) S := by
          simpa using ((hasDerivAt_id S).sub_const S).hasDerivWithinAt
        have hk : HasDerivWithinAt k
            (loewnerField W S (k S)) (Icc S (S + T)) S := by
          have hh := h.deriv 0 ⟨le_rfl, hT⟩
          have hraw := hh.scomp_of_eq S hinner hmap (by ring : (0 : ℝ) = S - S)
          convert hraw using 1
          simp [k]
        have hkvalue : k S = g.curve S := by simp [k, h.initial]
        have happLeft : EqOn (g.appendCurve h) g.curve (Icc (0 : ℝ) S) := by
          intro x hx
          simp [LoewnerForwardSolution.appendCurve, hx.2]
        have happRight : EqOn (g.appendCurve h) k (Icc S (S + T)) := by
          intro x hx
          rcases hx.1.eq_or_lt with rfl | hxlt
          · simp [LoewnerForwardSolution.appendCurve, k, h.initial]
          · simp [LoewnerForwardSolution.appendCurve, k, not_le.mpr hxlt]
        have hdl : HasDerivWithinAt (g.appendCurve h)
            (loewnerField W S ((g.appendCurve h) S)) (Icc (0 : ℝ) S) S := by
          have happS : (g.appendCurve h) S = g.curve S :=
            happLeft ⟨hS, le_rfl⟩
          rw [happS]
          exact (g.deriv S ⟨hS, le_rfl⟩).congr happLeft happS
        have hdr : HasDerivWithinAt (g.appendCurve h)
            (loewnerField W S ((g.appendCurve h) S)) (Icc S (S + T)) S := by
          have hk' : HasDerivWithinAt k
              (loewnerField W S (g.curve S)) (Icc S (S + T)) S := by
            rwa [hkvalue] at hk
          have happS : (g.appendCurve h) S = g.curve S := by
            simp [LoewnerForwardSolution.appendCurve]
          rw [happS]
          exact hk'.congr happRight (happRight ⟨le_rfl, by linarith⟩)
        have hdu := hdl.union hdr
        have hsets : Icc (0 : ℝ) S ∪ Icc S (S + T) = Icc 0 (S + T) := by
          ext x
          change ((0 ≤ x ∧ x ≤ S) ∨ (S ≤ x ∧ x ≤ S + T)) ↔
            (0 ≤ x ∧ x ≤ S + T)
          constructor
          · intro hx
            rcases hx with hx | hx
            · constructor <;> linarith [hx.1, hx.2, hT]
            · constructor <;> linarith [hx.1, hx.2, hS]
          · intro hx
            by_cases hxs : x ≤ S
            · exact Or.inl ⟨hx.1, hxs⟩
            · exact Or.inr ⟨le_of_not_ge hxs, hx.2⟩
        rwa [hsets] at hdu
  upper := by
    intro t ht
    by_cases hts : t ≤ S
    · simp only [LoewnerForwardSolution.appendCurve, if_pos hts]
      exact g.upper t ⟨ht.1, hts⟩
    · simp only [LoewnerForwardSolution.appendCurve, if_neg hts]
      exact h.upper (t - S) ⟨by linarith, by linarith [ht.2]⟩


end StatMech.SLE
