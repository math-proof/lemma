import Lemma.Hyperreal.EqSt
import Lemma.Hyperreal.Infinite.is.InfinitePow
import Lemma.Hyperreal.NotInfinite
import Lemma.Hyperreal.StMul.eq.MulStS.of.NotInfinite.NotInfinite
open Hyperreal


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h : ¬Hyperreal.Infinite x)
  (n : ℕ) :
-- imply
  (x ^ n).st = x.st ^ n := by
-- proof
  induction n with
  | zero =>
    simp
    apply EqSt
  | succ n ih =>
    simp [pow_succ]
    rw [← ih]
    apply StMul.eq.MulStS.of.NotInfinite.NotInfinite _ h
    if h_n : n = 0 then
      subst h_n
      simp
      apply NotInfinite
    else
      have : NeZero n := ⟨h_n⟩
      rwa [InfinitePow.is.Infinite]


-- created on 2025-12-16
-- updated on 2025-12-17
