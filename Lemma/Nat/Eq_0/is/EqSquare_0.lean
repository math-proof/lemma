import sympy.core.power
import Lemma.Nat.Eq_0.is.Pow.eq.Zero
import Lemma.Nat.EqPow0_0.of.Gt_0
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Eq_0.is.EqSquare_0 |
| mp 6  | Nat.NeSquare_0.of.Eq_0 |
| mpr | Nat.Eq_0.of.EqSquare_0 |
| mp.mt 6  | Nat.Ne_0.of.NeSquare_0 |
| mpr.mt | Nat.NeSquare_0.of.Ne_0 |
-/
@[main, mp 6, mpr, mp.mt 6, mpr.mt]
private lemma main
  [MonoidWithZero α]
  [NoZeroDivisors α]
  [NeZero (1 : α)]
-- given
  (x : α) :
-- imply
  x = 0 ↔ x² = 0 :=
-- proof
  ⟨(EqPow0_0.of.Gt_0.Eq_0 · two_pos), Eq_0.of.Pow.eq.Zero⟩


-- created on 2025-12-20
-- updated on 2026-08-22
