import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareSourcePhase
open StatMech StatMech.Universality


/--
[fkIsingSquareLiftedWinding_sub_eq_turnCount_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSourcePhase.lean)
-/
@[path]
private lemma fkIsingSquareLiftedWinding_sub_eq_turnCount_sub_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareLiftedWinding n hn omega x - fkIsingSquareLiftedWinding n hn omega y = ((fkIsingSquarePhysicalTurnCount n hn omega x - fkIsingSquarePhysicalTurnCount n hn omega y : Int) : Real) * (Real.pi / 4) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLiftedWinding_sub_eq_turnCount_sub n hn omega x y

/--
[fkIsingSquare_double_visit_open_source_side_membership](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSourcePhase.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_open_source_side_membership_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south)) < (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east))) ∧ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .west) ∨ (((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north)) < (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west))) ∧ fkIsingSquarePathUsesLocalSide n hn (setOpen e.1 omega) e .east) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_open_source_side_membership n hn omega e hwest heast

/--
[fkIsingSquare_double_visit_source_side_phase_of_discardedLoopTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareSourcePhase.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_source_side_phase_of_discardedLoopTurn_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hloop : FKIsingSquareDiscardedLoopTurn n hn omega e) :
-- imply
  (((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south)) < (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east))) ∧ (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .west)) = (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .west))) ∨ (((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north)) < (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west))) ∧ (fkIsingSquareDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .east)) = (fkIsingSquareDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .east))) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_source_side_phase_of_discardedLoopTurn n hn omega e hwest heast hloop


-- created on 2026-10-23
