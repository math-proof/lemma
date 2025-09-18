import Lemma.Algebra.AddMul.lt.Mul.of.Lt
open Algebra


@[main]
private lemma main
  {m n : ℕ}
-- given
  (h₀ : i < m)
  (h₁ : j  < n) :
-- imply
  i * n + j < m * n := by
-- proof
  let j : Fin n := ⟨j, h₁⟩
  have := AddMul.lt.Mul.of.Lt h₀ j
  simp_all
  assumption


-- created on 2025-06-14
