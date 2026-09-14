import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Rat.Eq_Div.is.EqMul.of.Ne_0 |
| comm | Rat.EqMul.is.Eq_Div.of.Ne_0 |
| mp   | Rat.EqMul.of.Eq_Div.Ne_0 |
| mpr  | Rat.Eq_Div.of.EqMul.Ne_0 |
| mp.comm | Rat.Eq_Mul.of.EqDiv.Ne_0 |
| mpr.comm | Rat.EqDiv.of.Eq_Mul.Ne_0 |
| comm.is | Rat.EqDiv.is.Eq_Mul.of.Ne_0 |
| mp.mt  | Rat.Ne_Div.of.NeMul.Ne_0 |
| mpr.mt | Rat.NeMul.of.Ne_Div.Ne_0 |
| is.mt  | Rat.Ne_Div.is.NeMul.of.Ne_0 |
-/
@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is, mp.mt, mpr.mt, is.mt]
private lemma main
  [GroupWithZero α]
  {b : α}
-- given
  (h₀ : b ≠ 0)
  (a c : α) :
-- imply
  a = c / b ↔ a * b = c :=
-- proof
  eq_div_iff h₀


@[main, comm, mp, mpr, mp.comm, mpr.comm, comm.is, mp.mt, mpr.mt, is.mt]
private lemma left
  [CommGroupWithZero α]
  {a : α}
-- given
  (h₀ : a ≠ 0)
  (c b : α):
-- imply
  b = c / a ↔ a * b = c := by
-- proof
  simpa [mul_comm] using eq_div_iff h₀


-- created on 2024-07-01
-- updated on 2025-12-10
