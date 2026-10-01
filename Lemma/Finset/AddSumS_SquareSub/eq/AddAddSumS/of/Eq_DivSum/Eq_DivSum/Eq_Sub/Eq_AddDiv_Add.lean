import sympy.sets.sets
import sympy.Basic


@[main]
private lemma parallel_variance
  {nA nB : ℕ}
  {xA xB : ℕ → ℝ}
  {a b c δ : ℝ}
-- given
  (h₀ : a = (∑ k ∈ Finset.range nA, xA k) / nA)
  (h₁ : b = (∑ k ∈ Finset.range nB, xB k) / nB)
  (h₂ : δ = b - a)
  (h₃ : c = a + δ * nB / (nA + nB)) :
-- imply
  ∑ k ∈ Finset.range nA, (xA k - c) ^ 2 + ∑ k ∈ Finset.range nB, (xB k - c) ^ 2 = ∑ k ∈ Finset.range nA, (xA k - a) ^ 2 + ∑ k ∈ Finset.range nB, (xB k - b) ^ 2 + δ ^ 2 * nA * nB / (nA + nB) := by
-- proof
  have expand : ∀ (m : ℕ) (z : ℕ → ℝ) (c : ℝ), ∑ k ∈ Finset.range m, (z k - c) ^ 2 = ∑ k ∈ Finset.range m, z k ^ 2 - 2 * c * ∑ k ∈ Finset.range m, z k + m * c ^ 2 := by
    intro m z c
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      push_cast
      ring
  have mean : ∀ (m : ℕ) (z : ℕ → ℝ) (c : ℝ), c = (∑ k ∈ Finset.range m, z k) / m → ∑ k ∈ Finset.range m, z k = m * c := by
    intro m z c hc
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · rw [hc]
      field_simp
  have hc : c = (nA * a + nB * b) / (nA + nB) := by
    rw [h₃, h₂]
    rcases Nat.eq_zero_or_pos (nA + nB) with hN | hN
    · have hA0 : nA = 0 := by omega
      have hB0 : nB = 0 := by omega
      subst hA0 hB0
      rw [h₀]
      simp
    · have hN' : ((nA : ℝ) + nB) ≠ 0 := by
        have : (0 : ℝ) < (nA : ℝ) + nB := by exact_mod_cast hN
        exact this.ne'
      field_simp
      ring
  rw [h₂]
  have hSA := mean nA xA a h₀
  have hSB := mean nB xB b h₁
  rw [expand, expand, expand, expand, hSA, hSB]
  rcases Nat.eq_zero_or_pos (nA + nB) with hN | hN
  · have hA0 : nA = 0 := by omega
    have hB0 : nB = 0 := by omega
    subst hA0 hB0
    simp
  · have hN' : ((nA : ℝ) + nB) ≠ 0 := by
      have : (0 : ℝ) < (nA : ℝ) + nB := by exact_mod_cast hN
      exact this.ne'
    rw [hc]
    field_simp
    ring


-- created on 2026-09-27
