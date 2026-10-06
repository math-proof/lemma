import Lemma.Tensor.Eq.of.DotStack_Pow
open Matrix


@[main]
private lemma main
  {n m : ℕ}
  {x y : Fin n → Fin m → ℂ}
-- given
  (h : ∀ (p : ℂ), p ≠ 0 →
    (fun k : Fin n => p ^ (k : ℕ)) ᵥ* x = (fun k : Fin n => p ^ (k : ℕ)) ᵥ* y) :
-- imply
  x = y := by
-- proof
  apply Tensor.Eq.of.DotStack_Pow.independence.matrix
  intro p hp j
  simpa [Matrix.vecMul, dotProduct] using congrFun (h p hp) j


-- created on 2023-04-08
-- updated on 2023-04-09
