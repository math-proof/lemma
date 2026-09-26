import Lemma.LpSpace.PowNorm.eq.Sum_PowAbs.of.Ge_1
import Lemma.Real.HasDerivAtPowAbs.of.Ge_2
open Finset LpSpace Real


@[main]
private lemma main
  {p d : ℕ}
  {x y : LpSpace p d}
  {t : ℝ}
-- given
  (h : 2 ≤ p) :
-- imply
  HasDerivAt (fun t : ℝ => ‖x + t • (y - x)‖ ^ p)
    (∑ i, p * |x i + t * (y i - x i)| ^ (p - 2) * (x i + t * (y i - x i)) * (y i - x i)) t := by
-- proof
  have hf : (fun t : ℝ => ‖x + t • (y - x)‖ ^ p) = fun t => ∑ i, |x i + t * (y i - x i)| ^ p := by
    funext t
    rw [PowNorm.eq.Sum_PowAbs.of.Ge_1 (by omega)]
    simp
  rw [hf]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have h₁ : HasDerivAt (fun t => x i + t * (y i - x i)) (y i - x i) t := by
    simpa using ((hasDerivAt_id' t).mul_const (y i - x i)).const_add (x i)
  exact (HasDerivAtPowAbs.of.Ge_2 h).comp t h₁


-- created on 2026-09-26