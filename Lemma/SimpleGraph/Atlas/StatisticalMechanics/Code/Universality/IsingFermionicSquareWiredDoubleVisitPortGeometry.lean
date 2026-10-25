import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredDoubleVisitPortGeometry.Part4
open StatMech StatMech.Universality


/--
[fkIsingSquareWired_double_visit_open_pair_exact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_open_pair_exact_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧ fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧ ¬fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧ ¬fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .south) ∨ (¬fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .west ∧ ¬fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .north ∧ fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .east ∧ fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .south) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_open_pair_exact n hn omega e hwest heast

/--
[fkIsingSquareWired_double_visit_discardedLoopTurn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_discardedLoopTurn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  FKIsingSquareWiredDiscardedLoopTurnModSixteen n hn omega e := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_discardedLoopTurn_mod_sixteen n hn omega e hwest heast

/--
[fkIsingSquareWired_double_visit_source_side_phase_of_discardedLoopTurn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_source_side_phase_of_discardedLoopTurn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hloop : FKIsingSquareWiredDiscardedLoopTurnModSixteen n hn omega e) :
-- imply
  (((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∧ (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .south)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .south))) ∨ (((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧ (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .north)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .north))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_source_side_phase_of_discardedLoopTurn_mod_sixteen n hn omega e hwest heast hloop

/--
[fkIsingSquareWired_double_visit_source_side_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_source_side_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∧ (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .south)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .south))) ∨ (((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧ (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .north)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .north))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_source_side_phase n hn omega e hwest heast

/--
[fkIsingSquareWired_double_visit_pointwise_contour_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_pointwise_contour_balance_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  let D := fkIsingSquareWiredDobrushinDomain n hn let closed := setClosed e.1 omega let opened := setOpen e.1 omega let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) (D.fermionicSummand closed W + D.fermionicSummand opened W) - (D.fermionicSummand closed E + D.fermionicSummand opened E) = Complex.I * ((D.fermionicSummand closed S + D.fermionicSummand opened S) - (D.fermionicSummand closed N + D.fermionicSummand opened N)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_pointwise_contour_balance n hn omega e hwest heast

/--
[fkIsingSquareWired_fermionicObservable_contour_relation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_fermionicObservable_contour_relation_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  let D := fkIsingSquareWiredDobrushinDomain n hn let edges := fkIsingSquareWiredLocalCarrierDarts n e D.fermionicObservable (edges 0) - D.fermionicObservable (edges 1) = Complex.I * (D.fermionicObservable (edges 2) - D.fermionicObservable (edges 3)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_fermionicObservable_contour_relation n hn e

/--
[fkIsingSquareWired_double_visit_discarded_carrier_cycle_turn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredDoubleVisitPortGeometry.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_discarded_carrier_cycle_turn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (∃ c : (fkIsingSquareWiredCompletedLoopGraph n hn (setOpen e.1 omega)).Walk (.dart (e, .west)) (.dart (e, .west)), c.IsCycle ∧ c.snd = (.dart (e, .north) : FKIsingSquareWiredCarrier n) ∧ carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) c.support ≡ 8 [ZMOD 16]) ∨ (∃ c : (fkIsingSquareWiredCompletedLoopGraph n hn (setOpen e.1 omega)).Walk (.dart (e, .east)) (.dart (e, .east)), c.IsCycle ∧ c.snd = (.dart (e, .south) : FKIsingSquareWiredCarrier n) ∧ carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) c.support ≡ 8 [ZMOD 16]) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_discarded_carrier_cycle_turn_mod_sixteen n hn omega e hwest heast


-- created on 2026-10-23
