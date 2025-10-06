import Lemma.Algebra.GtCoeS.is.Gt
import Lemma.Algebra.CoeAdd.eq.AddCoeS
import Lemma.Algebra.Cast_0.eq.Zero
import Lemma.Algebra.Cast_1.eq.One
open Algebra


@[main]
private lemma nat
-- given
  (n : ℕ) :
-- imply
  n + 1 > 0 := by
-- proof
  simp


@[main]
private lemma main
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
-- given
  (n : ℕ) :
-- imply
  n + 1 > (0 : R) := by
-- proof
  have h := nat n
  have h := GtCoeS.of.Gt.nat (R := R) h
  rw [CoeAdd.eq.AddCoeS.nat] at h
  rw [One.eq.Cast_1]
  rwa [Zero.eq.Cast_0]


-- created on 2025-05-28
-- updated on 2025-06-08
