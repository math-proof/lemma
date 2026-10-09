import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma series.arithmetic
  {k h : ℂ}
  {a b : ℤ}
-- given
  (h₀ : a ≤ b) :
-- imply
  ∑ i ∈ Finset.Ico a b, (k * i + h) = ((k * a + h) + (k * (b - 1) + h)) * (b - a) / 2 := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, b = a + m := ⟨(b - a).toNat, by omega⟩
  clear h₀
  induction m with
  | zero =>
    simp
  | succ m ih =>
    have e : Finset.Ico a (a + ((m + 1 : ℕ) : ℤ)) = insert (a + m) (Finset.Ico a (a + m)) := by
      ext x
      simp
      omega
    rw [e, Finset.sum_insert (by simp), ih]
    push_cast
    ring


@[path]
private lemma series.geometric
  {r : ℝ}
  {n : ℕ} :
-- imply
  ∑ k ∈ Finset.range n, r ^ k = if r = 1 then (n : ℝ) else (1 - r ^ n) / (1 - r) := by
-- proof
  split_ifs with h
  ·
    simp [h]
  ·
    rw [geom_sum_eq h]
    have h₁ : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have h₂ : r - 1 ≠ 0 := sub_ne_zero.mpr h
    field_simp
    ring


-- created on 2026-09-27
