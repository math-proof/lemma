import Lemma.Nat.Mul_Sub.eq.SubMulS
open Int Nat


@[main, comm]
private lemma main
  {x a : ℕ} :
-- imply
  x * a - x = x * (a - 1) := by
-- proof
  simp [Mul_Sub.eq.SubMulS]


-- created on 2026-08-02
