import Lemma.Nat.AddAdd.eq.Add_Add
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Nat.MulMul.eq.Mul_Mul
import Lemma.Nat.Square.eq.Mul
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Rat.Div1.eq.Inv
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivMulS.eq.Div.of.Ne_0
import sympy.core.power
open Nat Rat


@[main]
private lemma main
  [Semifield α]
  {a b : α}
-- given
  (h_a : a ≠ 0)
  (h_b : b ≠ 0) :
-- imply
  (1 + 2 * a * b) / (1 + a² + b²) = ((a * b)⁻¹ + 2) / ((a * b)⁻¹ + (a / b + b / a)) := by
-- proof
  have h_ab := Mul.ne.Zero.of.Ne_0.Ne_0 h_a h_b
  rw [Div.eq.DivDivS.of.Ne_0 h_ab]
  rw [DivAdd.eq.AddDivS]
  conv_lhs =>
    arg 2
    repeat rw [DivAdd.eq.AddDivS]
    repeat rw [Square.eq.Mul]
    rw [DivMulS.eq.Div.of.Ne_0 h_b]
    rw [DivMulS.eq.Div.of.Ne_0.left h_a]
  repeat rw [Div1.eq.Inv]
  rw [AddAdd.eq.Add_Add]
  rw [MulMul.eq.Mul_Mul]
  rw [EqDivMul.of.Ne_0 h_ab]


-- created on 2025-12-20
