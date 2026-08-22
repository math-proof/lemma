import sympy.Basic


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.EqPow0_0.of.Gt_0 |
| subst 0 | Nat.EqPow0_0.of.Gt_0.Eq_0 |
-/
@[main, subst 0]
private lemma main
  [MonoidWithZero α]
  {n : ℕ}
-- given
  (hn : n > 0) :
-- imply
  (0 : α) ^ n = 0 :=
-- proof
  zero_pow hn.ne'


-- created on 2018-11-03
-- updated on 2026-08-22
