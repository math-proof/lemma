import sympy.stats.hidden_markov_sequence
import sympy.core.numbers
import sympy.Basic
import Lemma.Random.IsHiddenMarkovFac.of.All_Eq.IsHiddenMarkovPr
open MeasureTheory
open scoped ENNReal.ToRealCoe


@[path]
private lemma crf.logits
  {Ω Y X : Type*} [MeasurableSpace Ω]
  [ReferenceMeasure Y] [ReferenceMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  {π : Measure Ω}
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {xo : ℕ → X}
  [∀ i, SinglePSpace π (y i)]
  [∀ i j, SinglePSpace π (x i, y j)]
  [∀ i j, SinglePSpace π (y i, y j)]
  [∀ n, SinglePSpace π (x[:n], y[:n])]
  {s : ℕ → (ℕ → Y) → ℝ}
  {e : ℕ → Y → ℝ}
  {G : Y → Y → ℝ}
-- given
  (h₀ : IsHiddenMarkovPr π x y xo)
  (h₁ : ∀ a, 0 < (ℙ[π]((y 0) = a) : ℝ))
  (h₂ : ∀ i a b, 0 < (ℙ[π]((y (i + 1)) = a | (y i) = b) : ℝ))
  (h₃ : ∀ t a, 0 < (ℙ[π]((x t) = xo t | (y t) = a) : ℝ))
  (h₄ : ∀ t ys, s t ys = (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ).log)
  (h₅ : ∀ t a, e t a = (ℙ[π]((x t) = xo t | (y t) = a) : ℝ).log)
  (h₆ : ∀ i a b, G a b = (ℙ[π]((y (i + 1)) = a | (y i) = b) : ℝ).log) :
-- imply
  ∀ ys : ℕ → Y, (∀ t, s (t + 1) ys = G (ys (t + 1)) (ys t) + s t ys + e (t + 1) (ys (t + 1))) ∧
    ∀ t, s t ys = (ℙ[π]((y 0) = ys 0) : ℝ).log + ∑ i ∈ Finset.Ico 1 (t + 1), G (ys i) (ys (i - 1)) + ∑ i ∈ Finset.range (t + 1), e i (ys i) := by
-- proof
  intro ys
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → (ℕ → Y) → ℝ, ∀ t ys, P t ys = (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ) := ⟨fun t ys => (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ), fun _ _ => rfl⟩
  have h₀ := Random.IsHiddenMarkovFac.of.All_Eq.IsHiddenMarkovPr h₀ hPdef
  have h₄ : ∀ t ys, s t ys = (P t ys).log := fun t ys => by rw [h₄, hPdef]
  have hP : ∀ t, 0 < P t ys := by
    intro t
    induction t with
    | zero =>
      rw [(h₀ ys).1]
      exact mul_pos (h₃ _ _) (h₁ _)
    | succ t ih =>
      rw [(h₀ ys).2 t]
      exact mul_pos ih (mul_pos (h₂ t _ _) (h₃ _ _))
  have hrec : ∀ t, s (t + 1) ys = G (ys (t + 1)) (ys t) + s t ys + e (t + 1) (ys (t + 1)) := by
    intro t
    have h2 := h₂ t (ys (t + 1)) (ys t)
    rw [h₄, h₄, h₅, h₆ t, (h₀ ys).2 t, Real.log_mul (hP t).ne' (mul_pos h2 (h₃ _ _)).ne', Real.log_mul h2.ne' (h₃ _ _).ne']
    ring
  refine ⟨hrec, fun t => ?_⟩
  induction t with
  | zero =>
    rw [h₄, (h₀ ys).1, Real.log_mul (h₃ _ _).ne' (h₁ _).ne']
    simp only [zero_add, Finset.Ico_self, Finset.sum_empty, Finset.sum_range_one, h₅]
    ring
  | succ t ih =>
    rw [hrec t, ih, Finset.sum_Ico_succ_top (by omega : 1 ≤ t + 1), Finset.sum_range_succ _ (t + 1), Nat.add_sub_cancel]
    ring


-- created on 2020-12-17
-- updated on 2025-04-20