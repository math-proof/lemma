import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[carrierAdjacentSum_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma carrierAdjacentSum_nil_eq
  {f : A → A → Int} :
-- imply
  carrierAdjacentSum f [] = 0 := by
-- proof
  apply StatMech.Universality.carrierAdjacentSum_nil f

/--
[carrierAdjacentSum_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma carrierAdjacentSum_singleton_eq
  {f : A → A → Int}
  {a : A} :
-- imply
  carrierAdjacentSum f [a] = 0 := by
-- proof
  apply StatMech.Universality.carrierAdjacentSum_singleton f a

/--
[carrierAdjacentSum_cons_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma carrierAdjacentSum_cons_cons_eq
  {f : A → A → Int}
  {a b : A}
  {l : List A} :
-- imply
  carrierAdjacentSum f (a :: b :: l) = f a b + carrierAdjacentSum f (b :: l) := by
-- proof
  apply StatMech.Universality.carrierAdjacentSum_cons_cons f a b l

/--
[carrierAdjacentSum_append_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma carrierAdjacentSum_append_cons_eq
  {f : A → A → Int}
  {l : List A}
  {a b : A}
  {r : List A} :
-- imply
  carrierAdjacentSum f (l ++ a :: b :: r) = carrierAdjacentSum f (l ++ [a]) + f a b + carrierAdjacentSum f (b :: r) := by
-- proof
  apply StatMech.Universality.carrierAdjacentSum_append_cons f l a b r

/--
[carrierAdjacentSum_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma carrierAdjacentSum_append_eq
  {f : A → A → Int}
  {l r : List A}
-- given
  (hl : l ≠ [])
  (hr : r ≠ []) :
-- imply
  carrierAdjacentSum f (l ++ r) = carrierAdjacentSum f l + f (l.getLast hl) (r.head hr) + carrierAdjacentSum f r := by
-- proof
  apply StatMech.Universality.carrierAdjacentSum_append f l r hl hr

/--
[wiredTurnSteps_drop_sum_eq_adjacentSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma wiredTurnSteps_drop_sum_eq_adjacentSum_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  ((fkIsingSquareWiredExplorationTurnSteps n hn omega).drop ((fkIsingSquareWiredExplorationOrder n hn omega).idxOf z)).sum = carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn omega) ((fkIsingSquareWiredExplorationOrder n hn omega).drop ((fkIsingSquareWiredExplorationOrder n hn omega).idxOf z)) := by
-- proof
  apply StatMech.Universality.wiredTurnSteps_drop_sum_eq_adjacentSum n hn omega z

/--
[FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi_mul_int](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma windingPhase_eq_of_winding_eq_add_four_pi_mul_int_eq
  {P : PlanarZ2Subgraph}
  [Fintype M]
  [DecidableEq M]
  {D : FKIsingDobrushinDomain P M}
  {omega omega' : ConfigSpace (Sym2 P.V)}
  {e e' : M}
  {k : Int}
-- given
  (h : D.winding omega' e' = D.winding omega e + (k : Real) * (4 * Real.pi)) :
-- imply
  D.windingPhase omega' e' = D.windingPhase omega e := by
-- proof
  apply StatMech.Universality.FKIsingDobrushinDomain.windingPhase_eq_of_winding_eq_add_four_pi_mul_int D omega omega' e e' k h

/--
[int_eighth_turn_mod_sixteen_of_exp_eq_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma int_eighth_turn_mod_sixteen_of_exp_eq_neg_one_eq
  {turn : Int}
-- given
  (hphase : Complex.exp (((((turn : Real) * (Real.pi / 8) : Real) : Complex) * Complex.I)) = -1) :
-- imply
  turn ≡ 8 [ZMOD 16] := by
-- proof
  apply StatMech.Universality.int_eighth_turn_mod_sixteen_of_exp_eq_neg_one turn hphase

/--
[fkIsingSquareWired_one_visit_west_inserted_phase_of_cycle_turn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_inserted_phase_of_cycle_turn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hcycle : ∀ (r : ((fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)).deleteEdges {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)), s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk (.dart (e, .east)) (.dart (e, .north))), r.IsPath → List.Disjoint (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)) r.support → carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support + fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .north)) (.dart (e, .east)) ≡ 8 [ZMOD 16]) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .south)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .south)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_inserted_phase_of_cycle_turn_mod_sixteen n hn omega e hwest heast hcycle

/--
[fkIsingSquareWired_one_visit_east_inserted_phase_of_cycle_turn_mod_sixteen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_inserted_phase_of_cycle_turn_mod_sixteen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hcycle : ∀ (r : ((fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)).deleteEdges {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)), s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk (.dart (e, .west)) (.dart (e, .south))), r.IsPath → List.Disjoint (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)) r.support → carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support + fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .south)) (.dart (e, .west)) ≡ 8 [ZMOD 16]) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .north)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_inserted_phase_of_cycle_turn_mod_sixteen n hn omega e hwest heast hcycle

/--
[fkIsingSquareWired_one_visit_west_inserted_phase_of_cycle_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_inserted_phase_of_cycle_turn_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hcycle : ∀ (r : ((fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)).deleteEdges {s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)), s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east))}).Walk (.dart (e, .east)) (.dart (e, .north))), r.IsPath → List.Disjoint (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)) r.support → carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support + fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .north)) (.dart (e, .east)) = 8 ∨ carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support + fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .north)) (.dart (e, .east)) = -8) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .south)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .south)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_inserted_phase_of_cycle_turn n hn omega e hwest heast hcycle

/--
[fkIsingSquareWired_one_visit_east_inserted_phase_of_cycle_turn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitInsertedPhase.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_inserted_phase_of_cycle_turn_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east)
  (hcycle : ∀ (r : ((fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega)).deleteEdges {s((.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)), s((.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west))}).Walk (.dart (e, .west)) (.dart (e, .south))), r.IsPath → List.Disjoint (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)) r.support → carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support + fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .south)) (.dart (e, .west)) = 8 ∨ carrierAdjacentSum (fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega)) r.support + fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) (.dart (e, .south)) (.dart (e, .west)) = -8) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .north)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .north)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_inserted_phase_of_cycle_turn n hn omega e hwest heast hcycle


-- created on 2026-10-23
