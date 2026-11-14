import Lemma.Tensor.DotT.eq.RotaryMatrixSub
import Notation.Data.Tensor.Permute
import Lemma.Tensor.SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge
import Instance.Data.Vector.Basic.Dot
open Tensor


@[path]
private lemma main
  {n d : ℕ}
  {θ : Tensor ℝ [n, d]}
  {τ : Tensor ℝ [d]}
  {k t : Fin n}
-- given
  (h : k ≥ t)
  (hθ : θ = [i < n] (τ * (i : ℝ))) :
-- imply
  θ[t].rotaryMatrixᵀ ⬝ᵥ θ[k].rotaryMatrix = θ[k - t].rotaryMatrix := by
-- proof
  apply Eq.trans (DotT.eq.RotaryMatrixSub θ[t] θ[k])
  exact congrArg rotaryMatrix (SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge h hθ)


-- created on 2023-09-16
-- updated on 2026-10-26
