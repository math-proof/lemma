import sympy.Basic

/--
| attributes | lemma |
| :---: | :---: |
| main | Int.LeCoeS.is.Le |
| comm | Int.Le.is.LeCoeS |
| mp   | Int.Le.of.LeCoeS |
| mpr  | Int.LeCoeS.of.Le |
| mp.comm | Int.Ge.of.GeCoeS |
| mpr.comm | Int.GeCoeS.of.Ge |
| comm.is | Int.GeCoeS.is.Ge |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
-- given
  (a b : ℤ) :
-- imply
  (a : R) ≤ (b : R) ↔ a ≤ b :=
-- proof
  Int.cast_le


-- created on 2025-10-16
