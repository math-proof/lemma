import Lemma.Nat.Ne_0.of.Gt
import Lemma.Nat.CoeMul.eq.MulCoeS
import Lemma.Int.EqToNat
import Lemma.Nat.CeilSub.eq.Sub_Floor
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Rat.FloorDiv.eq.Zero.of.Lt
import Lemma.Rat.Sub_Div.eq.DivSubMul.of.Ne_0
import sympy.vector.vector
open Int Nat Rat


@[main]
private lemma main
  {n : ℕ}
-- given
  (m : ℕ)
  (h : j < n) :
-- imply
  (⟨j, m * n, n⟩ : Slice).length (m * n) = m := by
-- proof
  have := Ne_0.of.Gt h
  simp [Slice.length]
  repeat rw [MulCoeS.eq.CoeMul]
  repeat rw [EqAdd_Mul_DivSub1Sign_2]
  repeat rw [EqToNat]
  simp
  rw [DivSubMul.eq.Sub_Div.of.Ne_0 (by simpa)]
  rw [@Nat.CeilSub.eq.Sub_Floor]
  simp [FloorDiv.eq.Zero.of.Lt h]


-- created on 2025-11-07
