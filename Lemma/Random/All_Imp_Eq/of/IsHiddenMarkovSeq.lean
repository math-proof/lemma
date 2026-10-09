import sympy.stats.hidden_markov_sequence
import sympy.Basic


/-- `P t` only depends on the prefix `ys 0, …, ys t`. -/
@[path]
private lemma main
  {P : ℕ → (ℕ → Y) → ℝ}
  {π : Y → ℝ}
  {T : Y → Y → ℝ}
  {E : ℕ → Y → ℝ}
-- given
  (h : IsHiddenMarkovSeq P π T E) :
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
