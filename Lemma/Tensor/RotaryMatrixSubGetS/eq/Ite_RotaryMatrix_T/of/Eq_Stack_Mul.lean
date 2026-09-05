import Lemma.Int.Sub.eq.NegSub
import Lemma.Tensor.RotaryMatrixNeg.eq.TRotaryMatrix
import Lemma.Tensor.SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge
open Int Tensor


@[main]
private lemma main
  {n d : ℕ}
  {θ : Tensor ℝ [n, d]}
  {τ : Tensor ℝ [d]}
  {i j : Fin n}
-- given
  (hθ : θ = [i < n] (τ * (i : ℝ))) :
-- imply
  (θ[j] - θ[i]).rotaryMatrix =
    if j ≥ i then
      θ[j - i].rotaryMatrix
    else
      θ[i - j].rotaryMatrixᵀ := by
-- proof
  by_cases h : j ≥ i
  ·
    erw [if_pos h]
    exact congrArg rotaryMatrix (SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge h hθ)
  ·
    erw [if_neg h]
    rw [(Sub.eq.NegSub θ[j] θ[i]).trans (congrArg Neg.neg (SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge (by grind) hθ))]
    apply RotaryMatrixNeg.eq.TRotaryMatrix


-- created on 2026-09-03
-- updated on 2026-09-05
