import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Sub.eq.Zero.is.Eq |
| comm | Int.Eq.is.Sub.eq.Zero |
| mp | Int.Eq.of.Sub.eq.Zero |
| mpr | Int.Sub.eq.Zero.of.Eq |
| mp.mt | Int.Sub.ne.Zero.of.Ne |
| mpr.mt | Int.Ne.of.Sub.ne.Zero |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [AddGroup α]
-- given
  (a b : α) :
-- imply
  a - b = 0 ↔ a = b :=
-- proof
  sub_eq_zero


-- created on 2025-03-20
-- updated on 2026-08-28
