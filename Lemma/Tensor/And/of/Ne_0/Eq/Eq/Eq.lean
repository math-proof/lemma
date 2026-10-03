import sympy.stats.hidden_markov_sequence
import sympy.concrete.max
import sympy.concrete.reduced
import sympy.stats.ennreal_coe
import sympy.Basic
open MeasureTheory
open scoped ENNReal.ToRealCoe


@[main]
private lemma crf.viterbi
  {Ω Y X : Type*} [MeasurableSpace Ω]
  [ReferenceMeasure Y] [ReferenceMeasure X]
  [Countable Y] [MeasurableSingletonClass Y] [Countable X] [MeasurableSingletonClass X]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {m : ℕ}
  {π : Measure Ω}
  {x : ℕ → Ω → X} {y : ℕ → Ω → Y} {xo : ℕ → X}
  [∀ i, SinglePSpace π (y i)]
  [∀ i j, SinglePSpace π (x i, y j)]
  [∀ i j, SinglePSpace π (y i, y j)]
  [∀ n, SinglePSpace π (x[:n], y[:n])]
  {s : ℕ → (ℕ → Y) → ℝ}
  {e : ℕ → Y → ℝ}
  {G : Y → Y → ℝ}
  {x' : ℕ → Y → ℝ}
-- given
  (h₀ : IsHiddenMarkovPr π x y xo)
  (h₁ : ∀ t (ys : ℕ → Y), 0 < (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ))
  (h₂ : ∀ t ys, s t ys = (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ).log)
  (h₃ : ∀ t a, e t a = (ℙ[π]((x t) = xo t | (y t) = a) : ℝ).log)
  (h₄ : ∀ i a b, G a b = (ℙ[π]((y (i + 1)) = a | (y i) = b) : ℝ).log)
  (h₅ : ∀ t a, x' t a = max[ys : Fin t → Y] s t (fun i => if h : i < t then ys ⟨i, h⟩ else a))
  (hT : ∀ i a b, 0 < (ℙ[π]((y (i + 1)) = a | (y i) = b) : ℝ))
  (hE : ∀ t a, 0 < (ℙ[π]((x t) = xo t | (y t) = a) : ℝ)) :
-- imply
  (∀ t a, x' (t + 1) a = e (t + 1) a + (x' t + G a).max) ∧
    max[ys : Fin (m + 1) → Y] (ℙ[π](x[:m + 1] = xo[:m + 1] ∧ y[:m + 1] = ys) : ℝ) =
      (x' m).max.exp := by
-- proof
  obtain ⟨P, hPdef⟩ : ∃ P : ℕ → (ℕ → Y) → ℝ, ∀ t ys, P t ys = (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ) := ⟨fun t ys => (ℙ[π](x[:t + 1] = xo[:t + 1] ∧ y[:t + 1] = ys[:t + 1]) : ℝ), fun _ _ => rfl⟩
  have h₁ : ∀ t ys, 0 < P t ys := fun t ys => by rw [hPdef]; exact h₁ t ys
  have h₀ := h₀.toFac hPdef
  have h₂ : ∀ t ys, s t ys = (P t ys).log := fun t ys => by rw [h₂, hPdef]
  have hpre := h₀.prefix
  have hTt := hT
  have hGt := h₄
  have hstep : ∀ t a b (ys0 : Fin t → Y),
      s (t + 1) (fun i => if h : i < t + 1 then Fin.snoc (α := fun _ => Y) ys0 b ⟨i, h⟩ else a) =
        s t (fun i => if h : i < t then ys0 ⟨i, h⟩ else b) + G a b + e (t + 1) a := by
    intro t a b ys0
    rw [h₂, h₂, (h₀ _).2 t, hpre t _ _ fun i hi => dite_snoc_eq ys0 b a hi]
    rw [dif_neg (lt_irrefl (t + 1)), dif_pos (Nat.lt_succ_self t), Fin.snoc_mk_last,
      Real.log_mul (h₁ _ _).ne' (mul_pos (hTt t a b) (hE _ a)).ne', Real.log_mul (hTt t a b).ne' (hE _ a).ne', hGt t a b, h₃]
    ring
  refine ⟨fun t a => ?_, ?_⟩
  ·
    rw [h₅, Finset.sup'_snoc]
    simp only [hstep, Finset.sup'_add_const_real]
    rw [add_comm]
    congr 1
    refine Finset.sup'_congr _ rfl fun b _ => ?_
    show _ = x' t b + G a b
    rw [h₅]
  ·
    have pad : ∀ (k : ℕ) (c : Y) (w : Fin k → Y), ((fun i : ℕ => if h : i < k then w ⟨i, h⟩ else c)[:k] : Fin k → Y) = w := by
      intro k c w
      funext i
      show (if h : i.val + 0 < k then w ⟨i.val + 0, h⟩ else c) = w i
      simp
    have e : ∀ ys : Fin (m + 1) → Y, (ℙ[π](x[:m + 1] = xo[:m + 1] ∧ y[:m + 1] = ys) : ℝ) = P (m + 1 - 1) (fun i => if h : i < m + 1 then ys ⟨i, h⟩ else Classical.arbitrary Y) := by
      intro ys
      rw [Nat.add_sub_cancel, hPdef]
      exact congrArg (fun w => (ℙ[π](x[:m + 1] = xo[:m + 1] ∧ y[:m + 1] = w) : ℝ)) (pad (m + 1) (Classical.arbitrary Y) ys).symm
    simp only [e]
    rw [Nat.add_sub_cancel, Finset.sup'_snoc, Function.max_eq,
      Finset.apply_sup'_eq_sup'_comp _ Real.exp (fun u v => Real.exp_monotone.map_sup u v)]
    refine Finset.sup'_congr _ rfl fun b _ => ?_
    rw [Function.comp_apply]
    show _ = Real.exp (x' m b)
    rw [h₅, Finset.apply_sup'_eq_sup'_comp _ Real.exp (fun u v => Real.exp_monotone.map_sup u v)]
    refine Finset.sup'_congr _ rfl fun ys0 _ => ?_
    rw [Function.comp_apply, h₂, Real.exp_log (h₁ _ _)]
    exact hpre m _ _ fun i hi => dite_snoc_eq ys0 b _ hi


-- created on 2020-12-20
-- updated on 2025-04-20