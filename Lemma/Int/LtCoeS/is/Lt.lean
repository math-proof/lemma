import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.LtCoeS.is.Lt |
| comm | Int.Lt.is.LtCoeS |
| mp   | Int.Lt.of.LtCoeS |
| mpr  | Int.LtCoeS.of.Lt |
| mp.comm | Int.Gt.of.GtCoeS |
| mpr.comm | Int.GtCoeS.of.Gt |
| comm.is | Int.GtCoeS.is.Gt |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R] [ZeroLEOneClass R]
  [NeZero (1 : R)]
-- given
  (a b : ℤ) :
-- imply
  (a : R) < (b : R) ↔ a < b :=
-- proof
  Int.cast_lt


-- created on 2025-10-16
