import Lemma.Nat.Mul
import Lemma.Nat.MulDivMulS.eq.Mul_MulDiv
open Nat


@[main]
private lemma main
-- given
  (n k d D : ℕ) :
-- imply
  n * (d * D) / (k * (d * D)) * (k * (d * D)) = d * (n * D / (k * D) * (k * D)) := by
-- proof
  if hz : d * D = 0 then
    obtain h | h := Nat.mul_eq_zero.mp hz
    · simp [h]
    · simp [h]
  else
    set z := d * D
    set y := k
    have h_lhs :
        n * (d * D) / (k * (d * D)) * (k * (d * D)) =
          z * (n / y * y) := by
      conv_lhs =>
        arg 1; arg 1
        rw [show n * (d * D) = z * n by dsimp [z]; ac_rfl]
      conv_lhs =>
        arg 1; arg 2
        rw [show k * (d * D) = z * y by dsimp [z, y]; ac_rfl]
      conv_lhs =>
        arg 2
        rw [show k * (d * D) = z * y by dsimp [z, y]; ac_rfl]
      rw [MulDivMulS.eq.Mul_MulDiv (x := n) (y := y)]
    have h_rhs :
        d * (n * D / (k * D) * (k * D)) =
          z * (n / y * y) := by
      have hinner :
          n * D / (k * D) * (k * D) =
            D * (n / y * y) := by
        conv_lhs =>
          arg 1; arg 1
          rw [show n * D = D * n by ac_rfl]
        conv_lhs =>
          arg 1; arg 2
          rw [show k * D = D * y by dsimp [y]; ac_rfl]
        conv_lhs =>
          arg 2
          rw [show k * D = D * y by dsimp [y]; ac_rfl]
        rw [MulDivMulS.eq.Mul_MulDiv (x := n) (y := y)]
      calc
        d * (n * D / (k * D) * (k * D))
            = d * (D * (n / y * y)) := by rw [hinner]
        _ = z * (n / y * y) := by dsimp [z]; rw [← Nat.mul_assoc]
    exact h_lhs.trans h_rhs.symm


-- created on 2026-08-03
