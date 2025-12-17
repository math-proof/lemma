import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.EqCoeS.is.Eq |
| comm | Rat.Eq.is.EqCoeS |
| mp | Rat.Eq.of.EqCoeS |
| mpr | Rat.EqCoeS.of.Eq |
| mp.mt | Rat.NeCoeS.of.Ne |
| mpr.mt | Rat.Ne.of.NeCoeS |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [DivisionRing R]
  [CharZero R]
  {a b : ℚ} :
-- imply
  (a : R) = (b : R) ↔ a = b :=
-- proof
  Rat.cast_inj


-- created on 2025-10-08
