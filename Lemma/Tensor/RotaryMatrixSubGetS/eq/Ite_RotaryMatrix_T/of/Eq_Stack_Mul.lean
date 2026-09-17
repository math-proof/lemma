import Lemma.Fin.NatAbsSub.eq.Sub.of.Ge
import Lemma.Fin.NatAbsSub.eq.Sub.of.Le
import Lemma.Fin.SignSub.eq.Neg1.of.Lt
import Lemma.Fin.SignSub.eq.One.of.Gt
import Lemma.Fin.SignSub.eq.Zero.of.Eq
import Lemma.Int.Sub.eq.NegSub
import Lemma.Tensor.MatPow.eq.Eye
import Lemma.Tensor.EqMatPow
import Lemma.Tensor.MatPow.eq.Inv
import Lemma.Tensor.RotaryMatrix0.eq.Eye
import Lemma.Tensor.RotaryMatrixNeg.eq.TRotaryMatrix
import Lemma.Tensor.InvRotaryMatrix.eq.TRotaryMatrix
import Lemma.Tensor.SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge
import sympy.matrices.expressions.matpow
open Fin Int Tensor


@[main]
private lemma main
  {n d : ℕ}
  {θ : Tensor ℝ [n, d]}
  {τ : Tensor ℝ [d]}
  {i j : Fin n}
-- given
  (hθ : θ = [i < n] (τ * (i : ℝ))) :
-- imply
  (θ[j] - θ[i]).rotaryMatrix = (θ[(j - i : ℤ).natAbs]'(by grind)).rotaryMatrix ^ (j - i : ℤ).sign := by
-- proof
  rcases lt_trichotomy j i with hlt | heq | hgt
  ·
    -- j < i
    rw [SignSub.eq.Neg1.of.Lt hlt]
    rw [show θ[(j - i : ℤ).natAbs]'(by grind) = θ[i - j] from by grind [NatAbsSub.eq.Sub.of.Le (le_of_lt hlt)]]
    rw [MatPow.eq.Inv.of.Eq_1 rfl]
    rw [(Sub.eq.NegSub θ[j] θ[i]).trans
      (congrArg Neg.neg (SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge (le_of_lt hlt) hθ))]
    exact Eq.trans (RotaryMatrixNeg.eq.TRotaryMatrix _) (InvRotaryMatrix.eq.TRotaryMatrix _).symm
  ·
    -- j = i
    rw [SignSub.eq.Zero.of.Eq heq]
    rw [MatPow.eq.Eye.of.Eq_0 rfl]
    rw [heq, sub_self]
    exact RotaryMatrix0.eq.Eye
  ·
    -- j > i
    rw [SignSub.eq.One.of.Gt hgt]
    rw [show θ[(j - i : ℤ).natAbs]'(by grind) = θ[j - i] from by grind [NatAbsSub.eq.Sub.of.Ge (le_of_lt hgt)]]
    rw [EqMatPow.of.Eq_1 rfl]
    exact congrArg rotaryMatrix (SubGetS.eq.Get_Sub.of.Eq_Stack_Mul.Ge (le_of_lt hgt) hθ)


-- created on 2026-09-03
-- updated on 2026-09-17
