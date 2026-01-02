import Lemma.Int.Sub.eq.NegSub
import Lemma.Real.Setoid.of.Eq
import Lemma.Tensor.ExpAdd_MulInfty.eq.Mul_Stack_Bool
import Lemma.Tensor.NegMul.eq.MulNeg
open Real Tensor Int


@[main]
private lemma main
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (A : Tensor ℝ [n, n]) :
-- imply
  let mask : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (p i j))
  let A : Tensor ℝ* [n, n] := A
  Exp.exp (A - (1 - mask) * Hyperreal.omega) ≈ exp A * mask := by
-- proof
  have := ExpAdd_MulInfty.eq.Mul_Stack_Bool p A
  simp
  symm
  apply this.symm.trans
  apply Setoid.of.Eq
  congr
  rw [@Tensor.NegMul.eq.MulNeg]
  rw [NegSub.eq.Sub]


-- created on 2026-01-02
