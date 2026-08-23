import Lemma.Nat.EqPow0_0.of.Gt_0
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Pow.eq.Zero.is.Eq_0.of.Gt_0 |
| comm | Nat.Eq_0.is.Pow.eq.Zero.of.Gt_0 |
| mp | Nat.Eq_0.of.Pow.eq.Zero.Gt_0 |
| mpr 6 | Nat.Pow.eq.Zero.of.Eq_0.Gt_0 |
| mp.mt | Nat.Pow.ne.Zero.of.Ne_0.Gt_0 |
| mpr.mt 6 | Nat.Ne_0.of.Pow.ne.Zero.Gt_0 |
-/
@[main, comm, mp, mpr 6, mp.mt, mpr.mt 6]
private lemma main
  [MonoidWithZero α]
  [NoZeroDivisors α]
  [NeZero (1 : α)]
  {x : α}
  {n : ℕ}
-- given
  (hn : n > 0) :
-- imply
  x ^ n = 0 ↔ x = 0 :=
-- proof
  ⟨(pow_eq_zero_iff hn.ne').mp, (EqPow0_0.of.Gt_0.Eq_0 · hn)⟩


-- created on 2018-11-03
-- updated on 2026-08-23
