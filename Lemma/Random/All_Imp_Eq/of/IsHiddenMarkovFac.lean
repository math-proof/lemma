import sympy.stats.hidden_markov_sequence
import sympy.Basic
open MeasureTheory
open scoped ENNReal.ToRealCoe


/-- `P t` only depends on the prefix `ys 0, …, ys t`. -/
@[path]
private lemma main
  [MeasurableSpace Ω]
  [ReferenceMeasure Y]
  [ReferenceMeasure X]
  {π : MeasureTheory.Measure Ω} {x : ℕ → Ω → X} {y : ℕ → Ω → Y} [∀ i, SinglePSpace π (y i)] [∀ i j, SinglePSpace π (x i, y j)] [∀ i j, SinglePSpace π (y i, y j)]
  {xo : ℕ → X}
  {P : ℕ → (ℕ → Y) → ℝ}
-- given
  (h : IsHiddenMarkovFac π x y xo P) :
-- imply
  ∀ t (w w' : ℕ → Y), (∀ i ≤ t, w i = w' i) → P t w = P t w' := by
-- proof
  intro t
  induction t with
  | zero =>
    intro w w' hw
    rw [(h w).1, (h w').1, hw 0 le_rfl]
  | succ t ih =>
    intro w w' hw
    rw [(h w).2 t, (h w').2 t, ih w w' (fun i hi => hw i (by omega)), hw t (by omega), hw (t + 1) le_rfl]


-- created on 2026-10-07
