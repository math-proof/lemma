import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | List.EqProd_0.is.In0 |
| comm | List.In0.is.EqProd_0 |
| mp | List.In0.of.EqProd_0 |
| mpr | List.EqProd_0.of.In0 |
| mp.mt | List.NeProd_0.of.NotIn0 |
| mpr.mt | List.NotIn0.of.NeProd_0 |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [MonoidWithZero M]
  [Nontrivial M]
  [NoZeroDivisors M]
-- given
  (l : List M) :
-- imply
  l.prod = 0 ↔ 0 ∈ l :=
-- proof
  List.prod_eq_zero_iff


-- created on 2025-08-02
