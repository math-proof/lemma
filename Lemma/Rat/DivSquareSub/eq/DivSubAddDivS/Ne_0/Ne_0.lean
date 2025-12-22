import Lemma.Int.MulSubS.eq.SubAddSMulS
import Lemma.Int.SquareSub
import Lemma.Nat.Add
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Nat.Square.eq.Mul
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivMulS.eq.Div.of.Ne_0
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.MulDivS.eq.DivMulS
import Lemma.Rat.MulDivS.eq.One.of.Ne_0.Ne_0
open Int Nat Rat


@[main]
private lemma main
  [Field α]
  {a b : α}
-- given
  (h_a : a ≠ 0)
  (h_b : b ≠ 0) :
-- imply
  (a - b)² / (a² + b² + 1) = (b / a + a / b - 2) / (b / a + a / b + 1 / (a * b)) := by
-- proof
  have h_ab_ne_0 := Mul.ne.Zero.of.Ne_0.Ne_0 h_a h_b
  rw [SquareSub.comm]
  rw [Add.comm (a := a²)]
  rw [Div.eq.DivDivS.of.Ne_0 h_ab_ne_0]
  repeat rw [Square.eq.Mul]
  rw [DivMulS.eq.MulDivS]
  repeat rw [DivAdd.eq.AddDivS]
  rw [DivSub.eq.SubDivS]
  rw [DivSub.eq.SubDivS]
  rw [DivMulS.eq.Div.of.Ne_0 (by assumption)]
  rw [DivMulS.eq.Div.of.Ne_0.left (by assumption)]
  repeat rw [Div.eq.One.of.Ne_0 (by assumption)]
  rw [MulSubS.eq.SubAddSMulS]
  rw [MulDivS.eq.One.of.Ne_0.Ne_0 (by assumption) (by assumption)]
  conv =>
    arg 1
    arg 1
    norm_num


-- created on 2025-12-21
