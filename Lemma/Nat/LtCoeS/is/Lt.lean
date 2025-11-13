import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.LtCoeS.is.Lt |
| comm | Nat.Lt.is.LtCoeS |
| mp   | Nat.Lt.of.LtCoeS |
| mpr  | Nat.LtCoeS.of.Lt |
| mp.comm | Nat.Gt.of.GtCoeS |
| mpr.comm | Nat.GtCoeS.of.Gt |
| comm.is | Nat.GtCoeS.is.Gt |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddMonoidWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [CharZero R]
-- given
  (a b : ℕ) :
-- imply
  (a : R) < (b : R) ↔ a < b :=
-- proof
  Nat.cast_lt


-- created on 2025-03-29
-- updated on 2025-10-16
