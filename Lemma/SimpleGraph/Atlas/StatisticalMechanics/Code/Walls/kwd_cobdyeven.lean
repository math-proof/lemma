import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kwd_cobdyeven.Part2
open Finset SimpleGraph StatMech StatMech.Walls


/--
[colourDisagrees_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_cobdyeven.lean)
-/
@[path]
private lemma colourDisagrees_mk_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  {c : V → Bool}
  {u v : V} :
-- imply
  colourDisagrees c s(u, v) ↔ c u ≠ c v := by
-- proof
  apply StatMech.Walls.colourDisagrees_mk c u v

/--
[mem_coboundary_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_cobdyeven.lean)
-/
@[path]
private lemma mem_coboundary_iff_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  [Fintype V]
  [DecidableRel Gp.Adj]
  {c : V → Bool}
  {u v : V}
-- given
  (h : Gp.Adj u v) :
-- imply
  s(u, v) ∈ coboundary Gp c ↔ c u ≠ c v := by
-- proof
  apply StatMech.Walls.mem_coboundary_iff c h

/--
[coboundary_subset_edgeFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_cobdyeven.lean)
-/
@[path]
private lemma coboundary_subset_edgeFinset_eq
  [DecidableEq V]
  {Gp : SimpleGraph V}
  [Fintype V]
  [DecidableRel Gp.Adj]
  {c : V → Bool} :
-- imply
  coboundary Gp c ⊆ Gp.edgeFinset := by
-- proof
  apply StatMech.Walls.coboundary_subset_edgeFinset c

/--
[walkParity_coboundary_eq_xor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_cobdyeven.lean)
-/
@[path]
private lemma walkParity_coboundary_eq_xor_eq
  [Fintype V]
  [DecidableEq V]
  {Gp : SimpleGraph V}
  [DecidableRel Gp.Adj]
  {c : V → Bool}
  {x y : V}
  {p : Gp.Walk x y} :
-- imply
  StatMech.Ising.walkParity Gp (coboundary Gp c) p = (c x).xor (c y) := by
-- proof
  apply StatMech.Walls.walkParity_coboundary_eq_xor c p

/--
[evenOnCycles_coboundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_cobdyeven.lean)
-/
@[path]
private lemma evenOnCycles_coboundary_eq
  [Fintype V]
  [DecidableEq V]
  {Gp : SimpleGraph V}
  [DecidableRel Gp.Adj]
  {c : V → Bool} :
-- imply
  StatMech.Ising.EvenOnCycles Gp (coboundary Gp c) := by
-- proof
  apply StatMech.Walls.evenOnCycles_coboundary c

/--
[walkParity_coboundary_loop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_cobdyeven.lean)
-/
@[path]
private lemma walkParity_coboundary_loop_eq
  [Fintype V]
  [DecidableEq V]
  {Gp : SimpleGraph V}
  [DecidableRel Gp.Adj]
  {c : V → Bool}
  {x : V}
  {p : Gp.Walk x x} :
-- imply
  StatMech.Ising.walkParity Gp (coboundary Gp c) p = false := by
-- proof
  apply StatMech.Walls.walkParity_coboundary_loop c p

/--
[coboundary_eq_cutEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_cobdyeven.lean)
-/
@[path]
private lemma coboundary_eq_cutEdges_eq
  [Fintype V]
  [DecidableEq V]
  {Gp : SimpleGraph V}
  [DecidableRel Gp.Adj]
  {c : V → Bool} :
-- imply
  coboundary Gp c = StatMech.Ising.cutEdges Gp c := by
-- proof
  apply StatMech.Walls.coboundary_eq_cutEdges c

/--
[evenOnCycles_cutEdges'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_cobdyeven.lean)
-/
@[path]
private lemma evenOnCycles_cutEdges'_eq
  [Fintype V]
  [DecidableEq V]
  {Gp : SimpleGraph V}
  [DecidableRel Gp.Adj]
  {c : V → Bool} :
-- imply
  StatMech.Ising.EvenOnCycles Gp (StatMech.Ising.cutEdges Gp c) := by
-- proof
  apply StatMech.Walls.evenOnCycles_cutEdges' c


-- created on 2026-10-23
