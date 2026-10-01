import Mathlib.Data.Matrix.Mul
import sympy.sets.sets
import sympy.Basic
open Matrix


@[main]
private lemma main
  {n m : ℕ}
  {S : Set (Fin n → ℤ)}
  {w : ℕ → Fin n → Matrix (Fin n) (Fin n) ℤ}
  {b : ℕ → Fin n}
-- given
  (h : ∀ x ∈ S, ∀ i j, x ᵥ* w i j ∈ S) :
-- imply
  ∀ x ∈ S, x ᵥ* ((List.range m).map fun i => w i (b i)).prod ∈ S := by
-- proof
  intro x hx
  induction m with
  | zero =>
    simpa using hx
  | succ m ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ← Matrix.vecMul_vecMul, List.map_singleton,
      List.prod_singleton]
    exact h _ ih m (b m)


-- created on 2026-09-27
