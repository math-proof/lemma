import sympy.concrete.continued_fraction
import sympy.Basic
open Continuant


@[path]
private lemma main
-- given
  (x y : ℕ → ℝ)
  (n : ℕ)
  (hxy : ∀ j, 1 ≤ j → j < n → x j = y j) :
-- imply
  ∀ m, m + 1 ≤ n → (K x m = K y m ∧ H x m = H y m + (x 0 - y 0) * K y m) ∧
      (K x (m + 1) = K y (m + 1) ∧ H x (m + 1) = H y (m + 1) + (x 0 - y 0) * K y (m + 1)) := by
-- proof
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨⟨rfl, by simp [H, K]⟩, rfl, by simp [H, K]⟩
  | succ m ih =>
    intro hm
    obtain ⟨h0, h1⟩ := ih (by omega)
    refine ⟨h1, ?_⟩
    have e := hxy (m + 1) (by omega) (by omega)
    show K x (m + 1) * x (m + 1) + K x m = K y (m + 1) * y (m + 1) + K y m ∧
      H x (m + 1) * x (m + 1) + H x m = H y (m + 1) * y (m + 1) + H y m + (x 0 - y 0) * (K y (m + 1) * y (m + 1) + K y m)
    rw [h0.1, h1.1, h0.2, h1.2, e]
    constructor
    · rfl
    · ring


-- created on 2026-10-07
