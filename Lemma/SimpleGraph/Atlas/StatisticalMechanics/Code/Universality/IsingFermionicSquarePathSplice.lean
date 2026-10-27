import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquarePathSplice
open Finset SimpleGraph StatMech StatMech.Universality


/--
[fkIsingSquare_sourceTerminalPath_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePathSplice.lean)
-/
@[path]
private lemma fkIsingSquare_sourceTerminalPath_unique_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {p q : (fkIsingSquareLoopGraph n hn omega).Walk (.source : FKIsingSquareMedialCarrier n) .terminal}
-- given
  (hn : 0 < n)
  (hp : p.IsPath)
  (hq : q.IsPath) :
-- imply
  p = q := by
-- proof
  apply StatMech.Universality.fkIsingSquare_sourceTerminalPath_unique n hn omega p q hp hq

/--
[fkIsingSquare_double_visit_open_splice_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePathSplice.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_open_splice_support_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  ((fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) = (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).take ((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west)) + 1) ++ (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).drop ((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north)))) ∧ (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south)) < (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east))) ∨ ((fkIsingSquareExplorationOrder n hn (setOpen e.1 omega) = (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).take ((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east)) + 1) ++ (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).drop ((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south)))) ∧ (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north)) < (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west))) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_open_splice_support n hn omega e hwest heast

/--
[fkIsingSquareLiftedWinding_eq_neg_suffix_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePathSplice.lean)
-/
@[path]
private lemma fkIsingSquareLiftedWinding_eq_neg_suffix_sum_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n)
  (hz : z ∈ fkIsingSquareExplorationOrder n hn omega) :
-- imply
  fkIsingSquareLiftedWinding n hn omega z = (-(((fkIsingSquareExplorationTurnSteps n hn omega).drop ((fkIsingSquareExplorationOrder n hn omega).idxOf z)).sum) : Real) * (Real.pi / 4) := by
-- proof
  apply StatMech.Universality.fkIsingSquareLiftedWinding_eq_neg_suffix_sum n hn omega z hz

/--
[fkIsingSquareExplorationTransitionTurn_open_eq_closed_of_nonlocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePathSplice.lean)
-/
@[path]
private lemma fkIsingSquareExplorationTransitionTurn_open_eq_closed_of_nonlocal_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {x y : FKIsingSquareMedialCarrier n}
-- given
  (hn : 0 < n)
  (hnonlocal : ∀ side, x = .dart (e, side) → ∀ side', y ≠ .dart (e, side')) :
-- imply
  fkIsingSquareExplorationTransitionTurn n hn (setOpen e.1 omega) x y = fkIsingSquareExplorationTransitionTurn n hn (setClosed e.1 omega) x y := by
-- proof
  apply StatMech.Universality.fkIsingSquareExplorationTransitionTurn_open_eq_closed_of_nonlocal n hn omega e x y hnonlocal

/--
[fkIsingSquare_double_visit_terminal_side_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquarePathSplice.lean)
-/
@[path]
private lemma fkIsingSquare_double_visit_terminal_side_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquarePathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south)) < (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east))) ∧ fkIsingSquareLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .north)) = fkIsingSquareLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .north))) ∨ (((fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north)) < (fkIsingSquareExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west))) ∧ fkIsingSquareLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .south)) = fkIsingSquareLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .south))) := by
-- proof
  apply StatMech.Universality.fkIsingSquare_double_visit_terminal_side_winding n hn omega e hwest heast


-- created on 2026-10-23
