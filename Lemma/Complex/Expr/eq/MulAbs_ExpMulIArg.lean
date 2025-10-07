import Lemma.Complex.ExpMulI.eq.AddCos_MulISin
import Lemma.Algebra.Expr.eq.AddRe_MulIIm
import Lemma.Bool.Eq.of.Eq.Eq
import Lemma.Algebra.Mul_Add.eq.AddMulS
import Lemma.Complex.Re.eq.MulAbs_CosArg
import Lemma.Complex.Im.eq.MulAbs_SinArg
import Lemma.Algebra.Eq.of.EqReS.EqImS
open Algebra Bool Complex


@[main]
private lemma main
  {z : ℂ} :
-- imply
  z = ‖z‖ * (I * arg z).exp := by
-- proof
  rw [ExpMulI.eq.AddCos_MulISin]
  apply Eq.of.Eq.Eq (f := fun z _ => ↑z.re + I * ↑z.im) (h_a := (Expr.eq.AddRe_MulIIm (z := z)).symm)
  rw [Mul_Add.eq.AddMulS]
  apply Eq.of.EqReS.EqImS
  simp at *
  have h_Eq : (z.arg : ℂ).cos.re = z.arg.cos := by
    simp [Real.cos]
  rw [h_Eq]
  apply Re.eq.MulAbs_CosArg (z := z)
  simp at *
  have h_Eq : (z.arg : ℂ).sin.re = z.arg.sin := by
    simp [Real.sin]
  rw [h_Eq]
  apply Im.eq.MulAbs_SinArg (z := z)


-- created on 2025-01-13
