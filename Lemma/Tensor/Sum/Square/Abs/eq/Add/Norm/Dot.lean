import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {k t : ℕ}
  {ξ : ℕ → ℂ}
  {L : ℕ → ℕ → ℂ} :
-- imply
  √(∑ c ∈ Finset.range k, ‖∑ r ∈ Finset.Ico k t, ξ r * ~(L r c) + ~(L t c)‖ ^ 2) ^ 2 =
    √(∑ c ∈ Finset.range k, ‖∑ r ∈ Finset.Ico k t, ξ r * ~(L r c)‖ ^ 2) ^ 2 + √(∑ c ∈ Finset.range k, ‖L t c‖ ^ 2) ^ 2 +
      2 * (∑ c ∈ Finset.range k, (∑ r ∈ Finset.Ico k t, ξ r * ~(L r c)) * L t c).re := by
-- proof
  have e : ∀ (s : Finset ℕ) (f : ℕ → ℂ), √(∑ i ∈ s, ‖f i‖ ^ 2) ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 :=
    fun _ _ => Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  simp only [e, Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im]
  ring


@[main]
private lemma recursive
  {k t : ℕ}
  {ξ : ℕ → ℂ}
  {L : ℕ → ℕ → ℂ}
-- given
  (h : k < t) :
-- imply
  √(∑ c ∈ Finset.range k, ‖∑ r ∈ Finset.Ico k t, ξ r * ~(L r c) + ~(L t c)‖ ^ 2) ^ 2 =
    ‖ξ k‖ ^ 2 * √(∑ c ∈ Finset.range k, ‖L k c‖ ^ 2) ^ 2 + √(∑ c ∈ Finset.range k, ‖∑ r ∈ Finset.Ico (k + 1) t, ξ r * ~(L r c) + ~(L t c)‖ ^ 2) ^ 2 +
      2 * ((∑ c ∈ Finset.range k, (∑ r ∈ Finset.Ico (k + 1) t, ξ r * ~(L r c) + ~(L t c)) * L k c) * ~(ξ k)).re := by
-- proof
  have e : ∀ (s : Finset ℕ) (f : ℕ → ℂ), √(∑ i ∈ s, ‖f i‖ ^ 2) ^ 2 = ∑ i ∈ s, ‖f i‖ ^ 2 :=
    fun _ _ => Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  simp only [e, Finset.sum_eq_sum_Ico_succ_bot h, Complex.re_sum, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re, Complex.add_im]
  ring


@[main]
private lemma recursive.real
  {k t : ℕ}
  {ξ : ℕ → ℝ}
  {L : ℕ → ℕ → ℝ}
-- given
  (h : k < t) :
-- imply
  √(∑ c ∈ Finset.range k, |∑ r ∈ Finset.Ico k t, ξ r * L r c + L t c| ^ 2) ^ 2 =
    |ξ k| ^ 2 * √(∑ c ∈ Finset.range k, |L k c| ^ 2) ^ 2 + √(∑ c ∈ Finset.range k, |∑ r ∈ Finset.Ico (k + 1) t, ξ r * L r c + L t c| ^ 2) ^ 2 +
      2 * (∑ c ∈ Finset.range k, (∑ r ∈ Finset.Ico (k + 1) t, ξ r * L r c + L t c) * L k c) * ξ k := by
-- proof
  have e : ∀ (s : Finset ℕ) (f : ℕ → ℝ), √(∑ i ∈ s, |f i| ^ 2) ^ 2 = ∑ i ∈ s, |f i| ^ 2 :=
    fun _ _ => Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [e, e, e]
  simp only [sq_abs, Finset.sum_eq_sum_Ico_succ_bot h, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring


-- created on 2026-09-27
