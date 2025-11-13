import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.LeCoeS.is.Le |
| comm | Nat.Le.is.LeCoeS |
| mp   | Nat.Le.of.LeCoeS |
| mpr  | Nat.LeCoeS.of.Le |
| mp.comm | Nat.Ge.of.GeCoeS |
| mpr.comm | Nat.GeCoeS.of.Ge |
| comm.is | Nat.GeCoeS.is.Ge |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
-- given
  (a b : ℕ) :
-- imply
  (a : R) ≤ (b : R) ↔ a ≤ b :=
-- proof
  Nat.cast_le


-- created on 2025-03-29
-- updated on 2025-10-16
