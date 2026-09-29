import sympy.functions.elementary.conv
import sympy.Basic


@[main]
private lemma conv1d
  {m d d' : ℕ}
  {T : Type*} [Fintype T]
  {off : T → Fin 1 → ℤ}
  {x : Fin m → (Fin 1 → ℤ) → Fin d → ℝ}
  {w : T → Fin d → Fin d' → ℝ}
  {β ζ : Fin m → Fin 1 → ℤ}
  {M : Fin m → (Fin 1 → ℤ) → ℝ}
-- given
  (h : ∀ k p, M k p = if ∀ a, β k a ≤ p a ∧ p a < ζ k a then 1 else 0) :
-- imply
  ∀ k p s, convNd off (fun q c => x k q c * M k q) w p s * M k p =
    if ∀ a, β k a ≤ p a ∧ p a < ζ k a then convNd off (fun q c => if ∀ a, 0 ≤ q a ∧ q a < ζ k a - β k a then x k (q + β k) c else 0) w (p - β k) s else 0 := by
-- proof
  intro k p s
  rw [h k p]
  split_ifs with hp
  ·
    rw [mul_one]
    simp only [convNd]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun c _ => ?_
    rw [h k]
    by_cases hq : ∀ a, β k a ≤ (p + off t) a ∧ (p + off t) a < ζ k a
    ·
      have hq' : ∀ a, 0 ≤ (p - β k + off t) a ∧ (p - β k + off t) a < ζ k a - β k a := by
        intro a
        have := hq a
        simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
        omega
      have e : p - β k + off t + β k = p + off t := by abel
      rw [if_pos hq, if_pos hq', mul_one, e]
    ·
      have hq' : ¬∀ a, 0 ≤ (p - β k + off t) a ∧ (p - β k + off t) a < ζ k a - β k a := by
        intro H
        apply hq
        intro a
        have := H a
        simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
        omega
      rw [if_neg hq, if_neg hq', mul_zero]
  ·
    rw [mul_zero]


-- created on 2026-09-27
