import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitSplice
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[fkIsingSquareWired_winding_eq_of_terminal_suffix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_winding_eq_of_terminal_suffix_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {d : FKIsingSquareWiredCarrier n}
  {pre : List (FKIsingSquareWiredCarrier n)}
-- given
  (hn : 0 < n)
  (hdClosed : d ∈ fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega))
  (hdOpen : d ∈ fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega))
  (hdPrefix : d ∉ pre)
  (hcentralDrop : ∀ side, (.dart (e, side) : FKIsingSquareWiredCarrier n) ∉ (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).drop ((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf d + 1))
  (hsplice : fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) = pre ++ (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).drop ((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf d)) :
-- imply
  fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) d = fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) d := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_winding_eq_of_terminal_suffix n hn omega e d pre hdClosed hdOpen hdPrefix hcentralDrop hsplice

/--
[fkIsingSquareWired_one_visit_west_cycleArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_cycleArc_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) ∃ r : (H.deleteEdges {s(S, W), s(N, E)}).Walk E N, r.IsPath ∧ List.Disjoint (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)) r.support := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_cycleArc n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_west_open_splice_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_open_splice_support_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) ∃ r : (H.deleteEdges {s(S, W), s(N, E)}).Walk E N, r.IsPath ∧ List.Disjoint (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)) r.support ∧ fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) = (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).take ((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf S + 1) ++ r.support ++ (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).drop ((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf W) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_open_splice_support n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_west_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .west)) = fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .west)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_winding n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_west_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_west_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .west)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .west)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_west_phase n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_east_cycleArc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_cycleArc_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) ∃ r : (H.deleteEdges {s(N, E), s(S, W)}).Walk W S, r.IsPath ∧ List.Disjoint (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)) r.support := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_cycleArc n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_east_open_splice_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_open_splice_support_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  let H := fkIsingSquareWiredLoopGraph n hn (setClosed e.1 omega) let S : FKIsingSquareWiredCarrier n := .dart (e, .south) let W : FKIsingSquareWiredCarrier n := .dart (e, .west) let N : FKIsingSquareWiredCarrier n := .dart (e, .north) let E : FKIsingSquareWiredCarrier n := .dart (e, .east) ∃ r : (H.deleteEdges {s(N, E), s(S, W)}).Walk W S, r.IsPath ∧ List.Disjoint (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)) r.support ∧ fkIsingSquareWiredExplorationOrder n hn (setOpen e.1 omega) = (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).take ((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf N + 1) ++ r.support ++ (fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).drop ((fkIsingSquareWiredExplorationOrder n hn (setClosed e.1 omega)).idxOf E) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_open_splice_support n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_east_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_winding_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  fkIsingSquareWiredLiftedWinding n hn (setOpen e.1 omega) (.dart (e, .east)) = fkIsingSquareWiredLiftedWinding n hn (setClosed e.1 omega) (.dart (e, .east)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_winding n hn omega e hwest heast

/--
[fkIsingSquareWired_one_visit_east_phase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredOneVisitSplice.lean)
-/
@[path]
private lemma fkIsingSquareWired_one_visit_east_phase_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n)
  (hwest : ¬ fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .west)
  (heast : fkIsingSquareWiredPathUsesLocalSide n hn (setClosed e.1 omega) e .east) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setOpen e.1 omega) (.dart (e, .east)) = (fkIsingSquareWiredDobrushinDomain n hn).windingPhase (setClosed e.1 omega) (.dart (e, .east)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_one_visit_east_phase n hn omega e hwest heast


-- created on 2026-10-23
