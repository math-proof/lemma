import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kwd_walkparity
open Finset SimpleGraph StatMech StatMech.Walls


/--
[walkDis_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_walkparity.lean)
-/
@[path]
private lemma walkDis_nil_eq
  {Gp : SimpleGraph V}
  {s : V → Bool}
  {x : V} :
-- imply
  walkDis Gp s (.nil : Gp.Walk x x) = 0 := by
-- proof
  apply StatMech.Walls.walkDis_nil Gp s

/--
[walkDis_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_walkparity.lean)
-/
@[path]
private lemma walkDis_cons_eq
  {Gp : SimpleGraph V}
  {s : V → Bool}
  {u v w : V}
  {p : Gp.Walk v w}
-- given
  (h : Gp.Adj u v) :
-- imply
  walkDis Gp s (.cons h p) = (if s u ≠ s v then 1 else 0) + walkDis Gp s p := by
-- proof
  apply StatMech.Walls.walkDis_cons Gp s h p

/--
[walkDis_parity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_walkparity.lean)
-/
@[path]
private lemma walkDis_parity_eq
  {Gp : SimpleGraph V}
  {s : V → Bool}
  {Gp s}
  {x y : V}
  {p : Gp.Walk x y} :
-- imply
  walkDis Gp s p % 2 = (if s x ≠ s y then 1 else 0) := by
-- proof
  apply StatMech.Walls.walkDis_parity Gp s p

/--
[walkDis_closed_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_walkparity.lean)
-/
@[path]
private lemma walkDis_closed_even_eq
  {Gp : SimpleGraph V}
  {s : V → Bool}
  {Gp s}
  {x : V}
  {p : Gp.Walk x x} :
-- imply
  walkDis Gp s p % 2 = 0 := by
-- proof
  apply StatMech.Walls.walkDis_closed_even Gp s p

/--
[closedWalk_even_disagreements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_walkparity.lean)
-/
@[path]
private lemma closedWalk_even_disagreements_eq
  {Gp : SimpleGraph V}
  {s : V → Bool}
  {Gp s}
  {x : V}
  {p : Gp.Walk x x} :
-- imply
  Even (walkDis Gp s p) := by
-- proof
  apply StatMech.Walls.closedWalk_even_disagreements Gp s p

/--
[walkDis_eq_darts_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_walkparity.lean)
-/
@[path]
private lemma walkDis_eq_darts_sum_eq
  {Gp : SimpleGraph V}
  {s : V → Bool}
  {Gp s}
  {x y : V}
  {p : Gp.Walk x y} :
-- imply
  walkDis Gp s p = (p.darts.map (fun d => if s d.fst ≠ s d.snd then 1 else 0)).sum := by
-- proof
  apply StatMech.Walls.walkDis_eq_darts_sum Gp s p

/--
[closedWalk_even_dartsSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_walkparity.lean)
-/
@[path]
private lemma closedWalk_even_dartsSum_eq
  {Gp : SimpleGraph V}
  {s : V → Bool}
  {Gp s}
  {x : V}
  {p : Gp.Walk x x} :
-- imply
  Even (p.darts.map (fun d => if s d.fst ≠ s d.snd then 1 else 0)).sum := by
-- proof
  apply StatMech.Walls.closedWalk_even_dartsSum Gp s p

/--
[walkDis_eq_ising](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_walkparity.lean)
-/
@[path]
private lemma walkDis_eq_ising_eq
  {Gp : SimpleGraph V}
  {s : V → Bool}
  {x y : V}
  {p : Gp.Walk x y} :
-- imply
  walkDis Gp s p = StatMech.Ising.walkDis Gp s p := by
-- proof
  apply StatMech.Walls.walkDis_eq_ising Gp s p

/--
[closedWalk_even_disagreements_ising](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_walkparity.lean)
-/
@[path]
private lemma closedWalk_even_disagreements_ising_eq
  {Gp : SimpleGraph V}
  {s : V → Bool}
  {x : V}
  {p : Gp.Walk x x} :
-- imply
  StatMech.Ising.walkDis Gp s p % 2 = 0 := by
-- proof
  apply StatMech.Walls.closedWalk_even_disagreements_ising Gp s p


-- created on 2026-10-23
