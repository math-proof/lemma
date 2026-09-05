import Lemma.Tensor.DotT.eq.RotaryMatrix'Sub
import Lemma.Tensor.SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge
open Tensor


@[main]
private lemma main
  {n d : ℕ}
  {θ : Tensor ℝ [n, d]}
  {τ : Tensor ℝ [d]}
  {k t : Fin n}
-- given
  (h : k ≥ t)
  (hθ : θ = [i < n] (τ * (i : ℝ))) :
-- imply
  θ[t].rotaryMatrix'ᵀ @ θ[k].rotaryMatrix' = θ[k - t].rotaryMatrix' := by
-- proof
  apply Eq.trans (DotT.eq.RotaryMatrix'Sub θ[t] θ[k])
  apply congrArg rotaryMatrix' (SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge h hθ)


-- created on 2026-09-05
