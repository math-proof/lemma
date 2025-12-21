import sympy.core.power
import Lemma.Nat.Eq_0.is.Pow.eq.Zero
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Nat.Eq\_0.is.EqSquare\_0 |
| mp 6  | Nat.NeSquare\_0.of.Eq\_0 |
| mpr | Nat.Eq\_0.of.EqSquare\_0 |
| mp.mt 6  | Nat.Ne\_0.of.NeSquare\_0 |
| mpr.mt | Nat.NeSquare\_0.of.Ne\_0 |
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
  ⟨Pow.eq.Zero.of.Eq_0, Eq_0.of.Pow.eq.Zero⟩


-- created on 2025-12-20
