import Lemma.Int.EqToNat
import Lemma.List.EqLengthSlice_Mul
import Lemma.Nat.CoeMul.eq.MulCoeS
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.Mul
import Lemma.Rat.EqToNatCeilDivSubMul.of.Lt
open Int Nat Rat List


@[main]
private lemma main
  {i : ℕ}
-- given
  (h : i < n)
  (m : ℕ) :
-- imply
  (⟨i, m * n, n⟩ : Slice).length (m * n) = m := by
-- proof
  have := EqLengthSlice_Mul ⟨i, h⟩ m
  simp_all


@[main]
private lemma Comm
  {i : ℕ}
-- given
  (h : i < n)
  (m : ℕ) :
-- imply
  (⟨i, n * m, n⟩ : Slice).length (n * m) = m := by
-- proof
  have := EqLengthSlice_Mul.comm ⟨i, h⟩ m
  simp_all


-- created on 2025-11-09
-- updated on 2025-11-14
