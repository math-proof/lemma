import sympy.core.power
import Lemma.Int.Eq_0.is.Pow.eq.Zero
open Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.Eq\_0.is.EqSquare\_0 |
| comm | Int.EqSquare\_0.is.Eq\_0 |
| mp   | Int.EqSquare\_0.of.Eq\_0 |
| mpr  | Int.Eq\_0.of.EqSquare\_0 |
| mp.mt | Int.Ne\_0.of.NeSquare\_0 |
| mpr.mt | Int.NeSquare\_0.of.Ne\_0 |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
-- given
  (a : α) :
-- imply
  (a = 0) ↔ (a² = 0) :=
-- proof
  Eq_0.is.Pow.eq.Zero (n := 2) a


-- created on 2024-11-29
-- updated on 2025-12-20
