import sympy.sets.sets
import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Nat.Ne_0.is.Eq_odd |
| mp | Nat.Eq_odd.of.Ne_0 |
| mpr | Nat.Ne_0.of.Eq_odd |
-/
@[path, mp, mpr]
private lemma main
  {n : ℤ} :
-- imply
  n % 2 ≠ 0 ↔ n % 2 = 1 := by
-- proof
  omega


-- created on 2020-01-27
-- updated on 2026-10-07
