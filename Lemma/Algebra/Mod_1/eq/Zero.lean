import Lemma.Algebra.Mod.eq.Sub_MulDiv
import Lemma.Algebra.EqDiv_1
import Lemma.Algebra.EqMul_1
import Lemma.Algebra.Sub.eq.Zero
import Lemma.Algebra.Mod0.eq.Zero
open Algebra


@[main]
private lemma main
  [IntegerRing Z]
-- given
  (n : Z) :
-- imply
  n % 1 = 0 := by
-- proof
  by_cases h : n = 0
  ·
    subst h
    apply Mod0.eq.Zero
  ·
    rw [Mod.eq.Sub_MulDiv]
    rw [EqDiv_1.int]
    rw [EqMul_1]
    rw [Sub.eq.Zero.int]


-- created on 2025-07-11
