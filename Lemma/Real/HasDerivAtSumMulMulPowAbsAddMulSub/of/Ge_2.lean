import Mathlib.Analysis.Calculus.Deriv.Add
import Lemma.Real.HasDerivAtMulMulPowAbs.of.Ge_2
open Finset Real


@[main]
private lemma main
  {p d : ℕ}
  {x y : Fin d → ℝ}
  {t : ℝ}
-- given
  (h : 2 ≤ p) :
-- imply
  HasDerivAt (fun t : ℝ => ∑ i, p * |x i + t * (y i - x i)| ^ (p - 2) * (x i + t * (y i - x i)) * (y i - x i))
    (∑ i, p * (p - 1) * |x i + t * (y i - x i)| ^ (p - 2) * (y i - x i) ^ 2) t := by
-- proof
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h₁ : HasDerivAt (fun t => x i + t * (y i - x i)) (y i - x i) t := by
    simpa using ((hasDerivAt_id' t).mul_const (y i - x i)).const_add (x i)
  refine (((HasDerivAtMulMulPowAbs.of.Ge_2 h).comp t h₁).mul_const (y i - x i)).congr_deriv ?_
  ring


-- created on 2026-09-26