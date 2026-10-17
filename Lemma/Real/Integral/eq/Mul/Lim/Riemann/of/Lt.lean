import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.UniformSpace.Compact
import sympy.Basic
open intervalIntegral Filter Finset Metric MeasureTheory Set


@[path]
private lemma main
  {f : ℝ → ℝ} {a b : ℝ}
  (h₀ : a < b)
  (h₁ : ContinuousOn f (Icc a b)) :
-- imply
  (∫ x in a..b, f x) =
    (b - a) * limUnder atTop (fun n : ℕ =>
      (∑ k ∈ range n, f (a + (b - a) * (k : ℝ) / n)) / n) := by
-- proof
  let δ : ℝ := b - a
  have hδ : 0 < δ := sub_pos.2 h₀
  have huc : UniformContinuousOn f (Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous h₁
  let s : ℕ → ℝ := fun n => (∑ k ∈ range n, f (a + δ * (k : ℝ) / n)) / n
  have hT : Tendsto s atTop (nhds ((∫ x in a..b, f x) / δ)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨η, hη0, hdist⟩ := (Metric.uniformContinuousOn_iff.mp huc) (ε / 2) (by linarith)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, δ / η < N := exists_nat_gt (δ / η)
    refine ⟨N, ?_⟩
    intro n hn
    have hn0 : 0 < n := by
      have hpos : 0 < δ / η := div_pos hδ hη0
      have hN0 : 0 < N := by
        exact_mod_cast lt_trans hpos hN
      exact lt_of_lt_of_le hN0 hn
    have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
    have hmesh : δ / (n : ℝ) < η := by
      have hlt : δ / η < (n : ℝ) := by
        exact_mod_cast lt_of_lt_of_le hN (Nat.cast_le.mpr hn)
      rw [div_lt_iff₀ hη0] at hlt
      rw [div_lt_iff₀ hn0']
      linarith
    let p : ℕ → ℝ := fun k => a + δ * (k : ℝ) / n
    have hp0 : p 0 = a := by simp [p]
    have hpn : p n = b := by
      simp [p, δ]
      field_simp
      ring
    have hstep (k : ℕ) : p (k + 1) - p k = δ / n := by
      simp only [p, Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    have hmono (k : ℕ) : p k ≤ p (k + 1) := by
      apply sub_nonneg.mp
      rw [hstep]
      positivity
    have hab (k : ℕ) (hk : k < n) : a ≤ p k ∧ p (k + 1) ≤ b := by
      constructor
      ·
        simp [p]
        positivity
      ·
        have hk' : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.succ_le_of_lt hk
        have : δ * ((k + 1 : ℕ) : ℝ) / n ≤ δ := by
          rw [div_le_iff₀ hn0']
          nlinarith
        simp only [p]
        linarith
    have hsub (k : ℕ) (hk : k < n) : uIcc (p k) (p (k + 1)) ⊆ Icc a b := by
      intro x hx
      rw [uIcc_of_le (hmono k), Set.mem_Icc] at hx
      obtain ⟨hka, hkb⟩ := hab k hk
      constructor
      · linarith
      · linarith
    have hsumI :
      ∑ k ∈ range n, ∫ x in p k..p (k + 1), f x = ∫ x in a..b, f x := by
      rw [sum_integral_adjacent_intervals]
      · rw [hp0, hpn]
      ·
        intro k hk
        apply ContinuousOn.intervalIntegrable
        apply h₁.mono
        apply hsub k hk
    have herr (k : ℕ) (hk : k < n) :
      |∫ x in p k..p (k + 1), f x - f (p k)| ≤ (ε / 2) * (δ / n) := by
      have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := p k) (b := p (k + 1)) (C := ε / 2)
        (f := fun x => f x - f (p k)) ?_
      simp only [Real.norm_eq_abs] at hbound
      rw [hstep k, abs_of_nonneg (by positivity : 0 ≤ δ / n)] at hbound
      apply hbound
      intro x hx
      rw [Real.norm_eq_abs]
      have hxI : x ∈ Icc a b := by
        rw [uIoc_of_le (hmono k), Set.mem_Ioc] at hx
        obtain ⟨hka, hkb⟩ := hab k hk
        constructor
        · linarith
        · linarith
      have hpk : p k ∈ Icc a b := by
        obtain ⟨hka, hkb⟩ := hab k hk
        constructor
        · exact hka
        · linarith [hmono k]
      have hclose : dist x (p k) < η := by
        rw [uIoc_of_le (hmono k), Set.mem_Ioc] at hx
        rw [dist_eq_norm, Real.norm_eq_abs]
        rw [abs_of_nonneg (sub_nonneg.2 (le_of_lt hx.1))]
        have : x - p k ≤ δ / n := by linarith [hx.2, hstep k]
        linarith [hmesh]
      have hlt := hdist x hxI (p k) hpk hclose
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm] using hlt.le
    have hinterr : |(∫ x in a..b, f x) - δ * s n| ≤ δ * ε / 2 := by
      have hconst : δ * s n = ∑ k ∈ range n, ∫ x in p k..p (k + 1), f (p k) := by
        simp only [s, mul_div_assoc']
        rw [Finset.mul_sum, Finset.sum_div]
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [intervalIntegral.integral_const, hstep k]
        simp
        ring
      have hsplit :
        (∫ x in a..b, f x) - δ * s n =
          ∑ k ∈ range n, ∫ x in p k..p (k + 1), f x - f (p k) := by
        rw [← hsumI, hconst, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro k hk
        apply Eq.symm
        apply intervalIntegral.integral_sub
        ·
          apply ContinuousOn.intervalIntegrable
          apply h₁.mono
          apply hsub k (Finset.mem_range.1 hk)
        · apply intervalIntegrable_const
      rw [hsplit]
      have hle :
        |∑ k ∈ range n, ∫ x in p k..p (k + 1), f x - f (p k)| ≤
          ∑ k ∈ range n, (ε / 2) * (δ / n) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        apply Finset.sum_le_sum
        intro k hk
        simpa using herr k (Finset.mem_range.1 hk)
      have hconstsum : ∑ k ∈ range n, (ε / 2) * (δ / n) = δ * ε / 2 := by
        simp [Finset.sum_const, Finset.card_range]
        field_simp
      rw [hconstsum] at hle
      nlinarith
    rw [dist_eq_norm, Real.norm_eq_abs]
    have hsub' : |s n - (∫ x in a..b, f x) / δ| =
        |(∫ x in a..b, f x) - δ * s n| / δ := by
      rw [abs_sub_comm, ← abs_of_pos hδ, ← abs_div]
      rw [abs_of_pos hδ]
      congr 1
      field_simp
    rw [hsub']
    rw [div_lt_iff₀ hδ]
    nlinarith
  rw [hT.limUnder_eq]
  field_simp [hδ.ne']
  ring


-- created on 2026-10-11
-- updated on 2026-10-17
