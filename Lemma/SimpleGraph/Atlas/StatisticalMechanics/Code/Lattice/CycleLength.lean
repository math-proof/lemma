import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.CycleLength
open SimpleGraph SimpleGraph.Walk StatMech StatMech.Lattice


/--
[walk_split_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CycleLength.lean)
-/
@[path]
private lemma walk_split_dist_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u a b : V}
  {p : G.Walk u u}
-- given
  (ha : a ∈ p.support)
  (hb : b ∈ p.support) :
-- imply
  2 * G.dist a b ≤ p.length := by
-- proof
  apply StatMech.Lattice.walk_split_dist p ha hb

/--
[IsCycle.length_ge_two_mul_dist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/CycleLength.lean)
-/
@[path]
private lemma length_ge_two_mul_dist_eq
  [DecidableEq V]
  {G : SimpleGraph V}
  {u a b : V}
  {p : G.Walk u u}
-- given
  (_hc : p.IsCycle)
  (ha : a ∈ p.support)
  (hb : b ∈ p.support) :
-- imply
  2 * G.dist a b ≤ p.length := by
-- proof
  apply StatMech.Lattice.IsCycle.length_ge_two_mul_dist _hc ha hb


-- created on 2026-10-23
