import Lemma.Tensor.DotT.eq.RotaryMatrixSub
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
  θ[t].rotaryMatrixᵀ @ θ[k].rotaryMatrix = θ[k - t].rotaryMatrix := by
-- proof
  apply Eq.trans (DotT.eq.RotaryMatrixSub θ[t] θ[k])
  exact congrArg rotaryMatrix (SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge h hθ)


-- created on 2023-05-30
-- updated on 2026-09-05
