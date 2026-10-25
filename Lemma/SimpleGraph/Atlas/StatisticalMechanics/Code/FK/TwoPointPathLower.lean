import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.TwoPointPathLower
open SimpleGraph StatMech StatMech.FK


/--
[cFE_pow_walk_length_le_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointPathLower.lean)
-/
@[path]
private lemma cFE_pow_walk_length_le_twoPoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : Real}
  {x y : V}
  {w : G.Walk x y}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  cFE p q ^ w.length <= twoPointFun G p q x y := by
-- proof
  apply StatMech.FK.cFE_pow_walk_length_le_twoPoint G hp hp1 hq w


-- created on 2026-10-23
