import Lemma.Matrix.SwapMatrix.eq.Eye
import Mathlib.Algebra.BigOperators.Group.List.Basic
open Matrix


@[path]
private lemma main
  [Semiring α]
-- given
  (n : ℕ) :
-- imply
  (List.ofFn fun i : Fin n => swapMatrix (α := α) i i).prod =
    (1 : Matrix (Fin n) (Fin n) α) := by
-- proof
  apply List.prod_eq_one
  intro x hx
  rw [List.mem_ofFn] at hx
  obtain ⟨i, rfl⟩ := hx
  apply SwapMatrix.eq.Eye


-- created on 2026-10-31
