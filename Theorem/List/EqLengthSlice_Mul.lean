module

public import Theorem.Int.EqToNat
public import Theorem.Nat.CoeMul.eq.MulCoeS
public import Theorem.Nat.EqAdd_Mul_DivSub1Sign_2
public import Theorem.Rat.EqToNatCeilDivSubMul.of.Lt

public section

open Int Nat Rat


public theorem List.EqLengthSlice_Mul
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


public theorem List.EqLengthSlice_Mul.comm
-- given
  (i : Fin n)
  (m : ℕ) :
-- imply
  (⟨i, n * m, n⟩ : Slice).length (n * m) = m := by
-- proof
  have := EqLengthSlice_Mul i m
  rw [Mul.comm m n] at this
  rw [Mul.comm] at this
  exact this


-- created on 2025-11-14
