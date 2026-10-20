import Mathlib.Data.Nat.Factorial.Basic
import Lemma.Matrix.DetOfVecCons_FunPow.eq.MulMulPowSProd
open Matrix


@[path]
private lemma main
  {n : ℕ}
  {x₁ x₂ : ℝ}
-- given
  (_ : x₁ ≠ 0) :
-- imply
  (Matrix.of (Matrix.vecCons (fun j : Fin (n + 1) => x₂ ^ (j : ℕ))
      (fun (i : Fin n) (j : Fin (n + 1)) => (j : ℝ) ^ (i : ℕ) * x₁ ^ (j : ℕ)))).det =
    x₁ ^ (n.choose 2) * (x₁ - x₂) ^ n * ∏ i ∈ Finset.range n, (Nat.factorial i : ℝ) :=
-- proof
  DetOfVecCons_FunPow.eq.MulMulPowSProd


-- created on 2020-10-14
-- updated on 2026-10-17
