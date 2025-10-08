import Lemma.Algebra.GtCoeS.is.Gt
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Algebra.Cast_0.eq.Zero
import Lemma.Algebra.Cast_1.eq.One
import Lemma.Nat.GtAdd_1'0
open Algebra Nat


@[main]
private lemma main
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
-- given
  (n : ℕ) :
-- imply
  n + 1 > (0 : R) := by
-- proof
  have h := GtAdd_1'0 n
  have h := GtCoeS.of.Gt.nat (R := R) h
  rw [CoeAdd.eq.AddCoeS] at h
  rw [One.eq.Cast_1]
  rwa [Zero.eq.Cast_0]


-- created on 2025-05-28
-- updated on 2025-10-08
