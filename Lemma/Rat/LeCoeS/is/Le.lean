import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.LeCoeS.is.Le |
| comm | Rat.Le.is.LeCoeS |
| mp   | Rat.Le.of.LeCoeS |
| mpr  | Rat.LeCoeS.of.Le |
| mp.comm | Rat.Ge.of.GeCoeS |
| mpr.comm | Rat.GeCoeS.of.Ge |
| comm.is | Rat.GeCoeS.is.Ge |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is]
private lemma main
  [Field R] [LinearOrder R] [IsStrictOrderedRing R]
-- given
  (a b : ℚ) :
-- imply
  (a : R) ≤ (b : R) ↔ a ≤ b :=
-- proof
  Rat.cast_le


-- created on 2025-10-16
