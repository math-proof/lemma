import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPathSplice
open Finset SimpleGraph StatMech StatMech.Universality


/--
[fkIsingSquareWiredBondMate_cornerTurn_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondMate_cornerTurn_ne_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareSideCorner (fkIsingSquareWiredBondMate n hn d).2).2 ≠ (fkIsingSquareSideCorner d.2).2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondMate_cornerTurn_ne n hn d

/--
[fkIsingSquareWiredLoopGraph_adj_phase_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_adj_phase_succ_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
-- imply
  fkIsingSquareWiredCarrierPhase n y = fkIsingSquareWiredCarrierPhase n x + 1 ∨ fkIsingSquareWiredCarrierPhase n x = fkIsingSquareWiredCarrierPhase n y + 1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_adj_phase_succ n hn omega hxy

/--
[fkIsingSquareWiredLoopGraph_isAlternating_incidence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_isAlternating_incidence_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredLoopGraph n hn omega).IsAlternating (fkIsingSquareWiredIncidenceGraph n) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_isAlternating_incidence n hn omega

/--
[fkIsingSquareWiredLoopGraph_adj_oddClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWiredLoopGraph_adj_oddClass_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareWiredLoopGraph n hn omega).Adj x y) :
-- imply
  fkIsingSquareWiredCarrierOddClass n x ↔ ¬ fkIsingSquareWiredCarrierOddClass n y := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLoopGraph_adj_oddClass n hn omega hxy

/--
[fkIsingSquareWiredExplorationPath_oddClass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWiredExplorationPath_oddClass_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {i : Nat}
-- given
  (hn : 0 < n)
  (hi : i ≤ (fkIsingSquareWiredExplorationPath n hn omega : (fkIsingSquareWiredLoopGraph n hn omega).Walk .source .terminal).length) :
-- imply
  fkIsingSquareWiredCarrierOddClass n ((fkIsingSquareWiredExplorationPath n hn omega : (fkIsingSquareWiredLoopGraph n hn omega).Walk .source .terminal).getVert i) ↔ Odd i := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredExplorationPath_oddClass n hn omega i hi

/--
[fkIsingSquareWired_localMate_infix_of_counterclockwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_localMate_infix_of_counterclockwise_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {side : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hccw : (fkIsingSquareSideCorner side).2 = .counterclockwise)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn omega e side) :
-- imply
  [(.dart (FKIsingMedialDart.localMate omega (e, side)) : FKIsingSquareWiredCarrier n), .dart (e, side)] <:+: fkIsingSquareWiredExplorationOrder n hn omega := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_localMate_infix_of_counterclockwise n hn omega e side hccw h

/--
[fkIsingSquareWired_closed_south_west_oriented_infix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_closed_south_west_oriented_infix_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west) :
-- imply
  [(.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .west)] <:+: fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_closed_south_west_oriented_infix n hn omega e h

/--
[fkIsingSquareWired_closed_north_east_oriented_infix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_closed_north_east_oriented_infix_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  [(.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .east)] <:+: fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_closed_north_east_oriented_infix n hn omega e h

/--
[fkIsingSquareWired_open_north_west_oriented_infix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_north_west_oriented_infix_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .west) :
-- imply
  [(.dart (e, .north) : FKIsingSquareWiredCarrier n), .dart (e, .west)] <:+: fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_open_north_west_oriented_infix n hn omega e h

/--
[fkIsingSquareWired_open_south_east_oriented_infix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_open_south_east_oriented_infix_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (h : fkIsingSquareWiredPathUsesLocalSide n hn (setOpen e.1 omega) e .east) :
-- imply
  [(.dart (e, .south) : FKIsingSquareWiredCarrier n), .dart (e, .east)] <:+: fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_open_south_east_oriented_infix n hn omega e h

/--
[fkIsingSquareWired_double_visit_closed_order](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_closed_order_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north)) ∨ (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_closed_order n hn omega e hwest heast

/--
[fkIsingSquareWired_double_visit_open_splice_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_open_splice_support_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  ((fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) = (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).take ((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south)) + 1) ++ (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).drop ((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east)))) ∧ (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∨ ((fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) = (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).take ((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north)) + 1) ++ (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).drop ((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west)))) ∧ (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_open_splice_support n hn omega e hwest heast

/--
[fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {z : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hz : z ∈ fkIsingSquareWiredExplorationOrder n hn omega) :
-- imply
  fkIsingSquareWiredLiftedWinding n hn omega z = (-(((fkIsingSquareWiredExplorationTurnSteps n hn omega).drop ((fkIsingSquareWiredExplorationOrder n hn omega).idxOf z)).sum) : Real) * (Real.pi / 4) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredLiftedWinding_eq_neg_suffix_sum n hn omega z hz

/--
[fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hnonlocal : ∀ side, x = .dart (e, side) → ∀ side', y ≠ .dart (e, side')) :
-- imply
  fkIsingSquareWiredTransitionTurn n hn (setOpen e.1 omega) x y = fkIsingSquareWiredTransitionTurn n hn (setClosed e.1 omega) x y := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredTransitionTurn_open_eq_closed_of_nonlocal n hn omega e x y hnonlocal

/--
[fkIsingSquareWired_double_visit_terminal_side_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_terminal_side_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∧ fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .east)) = fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .east))) ∨ (((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧ fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .west)) = fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .west))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_terminal_side_winding n hn omega e hwest heast

/--
[fkIsingSquareWired_double_visit_terminal_side_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPathSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_double_visit_terminal_side_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .west)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .north))) ∧ (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .east)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .east))) ∨ (((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .east)) < (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf (.dart (e, .south))) ∧ (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .west)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .west))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_double_visit_terminal_side_phase n hn omega e hwest heast


-- created on 2026-10-23
