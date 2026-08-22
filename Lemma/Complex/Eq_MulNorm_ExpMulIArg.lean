import Lemma.Complex.ExpMulI.eq.AddCos_MulISin
import Lemma.Complex.Expr.eq.AddRe_MulIIm
import Lemma.Bool.Eq.of.Eq.Eq
import Lemma.Nat.Mul_Add.eq.AddMulS
import Lemma.Complex.Re.eq.MulNorm_CosArg
import Lemma.Complex.Im.eq.MulNorm_SinArg
import Lemma.Complex.Eq.of.Re.Im
open Bool Complex Nat


@[main]
private lemma main
  {z : ℂ} :
-- imply
  z = ‖z‖ * (I * arg z).exp := by
-- proof
  rw [ExpMulI.eq.AddCos_MulISin]
  apply Eq.of.Eq.Eq (f := fun z _ => ↑z.re + I * ↑z.im) (h_a := (Expr.eq.AddRe_MulIIm (z := z)).symm)
  rw [Mul_Add.eq.AddMulS]
  apply Eq.of.Re.Im
  simp at *
  have h_Eq : (z.arg : ℂ).cos.re = z.arg.cos := by
    simp [Real.cos]
  rw [h_Eq]
  apply Re.eq.MulNorm_CosArg (z := z)
  simp at *
  have h_Eq : (z.arg : ℂ).sin.re = z.arg.sin := by
    simp [Real.sin]
  rw [h_Eq]
  apply Im.eq.MulNorm_SinArg (z := z)


-- created on 2025-01-13
