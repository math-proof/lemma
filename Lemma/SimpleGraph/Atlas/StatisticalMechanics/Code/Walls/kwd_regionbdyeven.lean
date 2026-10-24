import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kwd_regionbdyeven
open Finset SimpleGraph StatMech StatMech.Walls


/--
[kwd_regionbdyeven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_regionbdyeven.lean)
-/
@[path]
private lemma kwd_regionbdyeven_eq
  [Fintype V]
  [DecidableEq V]
  {S : V → Bool} :
-- imply
  EvenOnCycles Gp (regionBoundary Gp S) := by
-- proof
  apply StatMech.Walls.kwd_regionbdyeven S

/--
[kwd_regionbdyeven_walkParity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_regionbdyeven.lean)
-/
@[path]
private lemma kwd_regionbdyeven_walkParity_eq
  [Fintype V]
  [DecidableEq V]
  {S : V → Bool}
  {x : V}
  {p : Gp.Walk x x} :
-- imply
  walkParity Gp (regionBoundary Gp S) p = false := by
-- proof
  apply StatMech.Walls.kwd_regionbdyeven_walkParity S p

/--
[kwd_regionbdyeven_mem_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_regionbdyeven.lean)
-/
@[path]
private lemma kwd_regionbdyeven_mem_iff_eq
  [Fintype V]
  [DecidableEq V]
  {S : V → Bool}
  {u v : V}
-- given
  (h : Gp.Adj u v) :
-- imply
  s(u, v) ∈ regionBoundary Gp S ↔ S u ≠ S v := by
-- proof
  apply StatMech.Walls.kwd_regionbdyeven_mem_iff S h


-- created on 2026-10-23
