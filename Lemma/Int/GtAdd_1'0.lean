import Lemma.Nat.LtCoeS.is.Lt
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Nat.EqCast_0'0
import Lemma.Nat.EqCast_1'1
import Lemma.Nat.GtAdd_1'0
open Nat


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
  have h := GtCoeS.of.Gt (R := R) h
  rw [CoeAdd.eq.AddCoeS] at h
  rw [← EqCast_1'1]
  rwa [← EqCast_0'0]


-- created on 2025-05-28
-- updated on 2025-10-08
