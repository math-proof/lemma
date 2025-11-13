import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.LtCoeS.is.Lt |
| comm | Rat.Lt.is.LtCoeS |
| mp   | Rat.Lt.of.LtCoeS |
| mpr  | Rat.LtCoeS.of.Lt |
| mp.comm | Rat.Gt.of.GtCoeS |
| mpr.comm | Rat.GtCoeS.of.Gt |
| comm.is | Rat.GtCoeS.is.Gt |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
-- given
  (a b : ℚ) :
-- imply
  (a : R) < (b : R) ↔ a < b :=
-- proof
  Rat.cast_lt


-- created on 2025-10-16
