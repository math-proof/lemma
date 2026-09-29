import sympy.stats.hidden_markov_sequence
import sympy.Basic


@[main]
private lemma crf.markov.logits
  {Y : Type*}
  {P : ℕ → (ℕ → Y) → ℝ}
  {π : Y → ℝ}
  {T : Y → Y → ℝ}
  {E : ℕ → Y → ℝ}
  {s : ℕ → (ℕ → Y) → ℝ}
  {x : ℕ → Y → ℝ}
  {G : Y → Y → ℝ}
-- given
  (h₀ : IsHiddenMarkovSeq P π T E)
  (h₁ : ∀ t ys, 0 < P t ys)
  (h₂ : ∀ a b, 0 < T a b)
  (h₃ : ∀ t a, 0 < E t a)
  (h₄ : ∀ t ys, s t ys = Real.log (P t ys))
  (h₅ : ∀ t a, x t a = Real.log (E t a))
  (h₆ : ∀ a b, G a b = Real.log (T b a)) :
-- imply
  ∀ (ys : ℕ → Y) (t : ℕ), 0 < t → s t ys = G (ys t) (ys (t - 1)) + s (t - 1) ys + x t (ys t) := by
-- proof
  intro ys t ht
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [Nat.add_sub_cancel, h₄, h₄, h₅, h₆, (h₀ ys).2 t, Real.log_mul (h₁ t ys).ne' (mul_pos (h₂ _ _) (h₃ _ _)).ne', Real.log_mul (h₂ _ _).ne' (h₃ _ _).ne']
  ring


-- created on 2026-09-27
