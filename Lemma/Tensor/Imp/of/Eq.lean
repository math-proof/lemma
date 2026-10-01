import sympy.stats.hidden_markov_sequence
import sympy.Basic


@[main]
private lemma crf.logits
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
  (h₁ : ∀ a, 0 < π a)
  (h₂ : ∀ a b, 0 < T a b)
  (h₃ : ∀ t a, 0 < E t a)
  (h₄ : ∀ t ys, s t ys = Real.log (P t ys))
  (h₅ : ∀ t a, x t a = Real.log (E t a))
  (h₆ : ∀ a b, G a b = Real.log (T b a)) :
-- imply
  ∀ ys : ℕ → Y, (∀ t, 0 < t → s t ys = G (ys t) (ys (t - 1)) + s (t - 1) ys + x t (ys t)) ∧
    ∀ t, s t ys = Real.log (π (ys 0)) + ∑ i ∈ Finset.Ico 1 (t + 1), G (ys i) (ys (i - 1)) + ∑ i ∈ Finset.range (t + 1), x i (ys i) := by
-- proof
  intro ys
  have hP : ∀ t, 0 < P t ys := by
    intro t
    induction t with
    | zero =>
      rw [(h₀ ys).1]
      exact mul_pos (h₃ _ _) (h₁ _)
    | succ t ih =>
      rw [(h₀ ys).2 t]
      exact mul_pos ih (mul_pos (h₂ _ _) (h₃ _ _))
  have hrec : ∀ t, 0 < t → s t ys = G (ys t) (ys (t - 1)) + s (t - 1) ys + x t (ys t) := by
    intro t ht
    obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [Nat.add_sub_cancel, h₄, h₄, h₅, h₆, (h₀ ys).2 t, Real.log_mul (hP t).ne' (mul_pos (h₂ _ _) (h₃ _ _)).ne', Real.log_mul (h₂ _ _).ne' (h₃ _ _).ne']
    ring
  refine ⟨hrec, fun t => ?_⟩
  induction t with
  | zero =>
    rw [h₄, (h₀ ys).1, Real.log_mul (h₃ _ _).ne' (h₁ _).ne']
    simp only [zero_add, Finset.Ico_self, Finset.sum_empty, Finset.sum_range_one, h₅]
    ring
  | succ t ih =>
    rw [hrec (t + 1) (by omega), Nat.add_sub_cancel, ih, Finset.sum_Ico_succ_top (by omega : 1 ≤ t + 1), Finset.sum_range_succ _ (t + 1), Nat.add_sub_cancel]
    ring


-- created on 2026-09-27
