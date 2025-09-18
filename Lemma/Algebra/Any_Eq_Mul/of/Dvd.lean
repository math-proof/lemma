import sympy.functions.elementary.integers
import Lemma.Algebra.Mul
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
  {x d : Z}
-- given
  (h : d ∣ x) :
-- imply
  ∃ k, x = d * k := by
-- proof
  exact h


@[main]
private lemma left
  [IntegerRing Z]
  {x d : Z}
-- given
  (h : d ∣ x) :
-- imply
  ∃ k, x = k * d := by
-- proof
  let ⟨k, h_eq⟩ := h
  rw [Mul.comm] at h_eq
  use k


-- created on 2025-07-08
