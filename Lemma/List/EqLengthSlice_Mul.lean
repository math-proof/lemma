import Lemma.Int.EqToNat
import Lemma.Nat.CoeMul.eq.MulCoeS
import Lemma.Nat.EqAdd_Mul_DivSub1Sign_2
import Lemma.Nat.Mul
import Lemma.Rat.EqToNatCeilDivSubMul.of.Lt
open Int Nat Rat


@[main]
private lemma main
-- given
  (i : Fin n)
  (m : ℕ) :
-- imply
  (⟨i, m * n, n⟩ : Slice).length (m * n) = m := by
-- proof
  unfold Slice.length
  simp [EqAdd_Mul_DivSub1Sign_2]
  repeat rw [MulCoeS.eq.CoeMul]
  rw [EqAdd_Mul_DivSub1Sign_2]
  rw [EqToNat]
  simp
  rw [EqToNatCeilDivSubMul.of.Lt]
  simp


@[main]
private lemma comm'
-- given
  (i : Fin n)
  (m : ℕ) :
-- imply
  (⟨i, n * m, n⟩ : Slice).length (n * m) = m := by
-- proof
  have := main i m
  rw [Mul.comm m n] at this
  rw [Mul.comm] at this
  exact this


-- created on 2025-11-14
