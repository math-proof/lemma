import Lemma.Algebra.LtDiv.of.Lt_Mul
import Lemma.Algebra.Mul
import Lemma.Algebra.Gt_0.of.Gt
import Lemma.Algebra.Gt_0.of.Mul.gt.Zero
import Lemma.Algebra.LtMod.of.Gt_0
import Lemma.Algebra.Eq_AddMulDiv___Mod
open Algebra


@[main]
private lemma main
  {m n : ℕ}
-- given
  (h : t < m * n) :
-- imply
  ∃ i < m, ∃ j < n, t = i * n + j := by
-- proof
  use t / n
  constructor
  ·
    apply LtDiv.of.Lt_Mul.left
    rwa [Mul.comm]
  ·
    use t % n
    constructor
    ·
      have := Gt_0.of.Gt h
      have := Gt_0.of.Mul.gt.Zero this
      apply LtMod.of.Gt_0 this
    ·
      apply Eq_AddMulDiv___Mod


-- created on 2025-06-13
