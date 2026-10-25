import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredRibbon.Part9
open Equiv SimpleGraph StatMech StatMech.Universality


/--
[fkIsingSquareWiredDartColor_localMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredDartColor_localMate_ne_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareWiredDartSideColor (FKIsingMedialDart.localMate omega d).2 ≠ fkIsingSquareWiredDartSideColor d.2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredDartColor_localMate_ne n omega d

/--
[fkIsingSquareWiredBondMate_turn_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondMate_turn_ne_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareSideCorner (fkIsingSquareWiredBondMate n hn d).2).2 ≠ (fkIsingSquareSideCorner d.2).2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondMate_turn_ne n hn d

/--
[fkIsingSquareWiredBondColor_bondMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredBondColor_bondMate_ne_eq
  {n : Nat}
  {d : FKIsingMedialDart (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  (!fkIsingSquareWiredTurnColor (fkIsingSquareSideCorner (fkIsingSquareWiredBondMate n hn d).2).2) ≠ !fkIsingSquareWiredTurnColor (fkIsingSquareSideCorner d.2).2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBondColor_bondMate_ne n hn d

/--
[fkIsingSquareWiredCarrierColor_completedIncidence_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredCarrierColor_completedIncidence_ne_eq
  {n : Nat}
  {x : FKIsingSquareWiredCarrier n} :
-- imply
  fkIsingSquareWiredCarrierColor n (fkIsingSquareWiredCompletedIncidenceEquiv n x) ≠ fkIsingSquareWiredCarrierColor n x := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCarrierColor_completedIncidence_ne n x

/--
[fkIsingSquareWiredCarrierColor_transition_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredCarrierColor_transition_ne_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredCarrierColor n (fkIsingSquareWiredTransitionEquiv n hn omega x) ≠ fkIsingSquareWiredCarrierColor n x := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCarrierColor_transition_ne n hn omega x

/--
[fkIsingSquareWiredCarrierColor_boundaryStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredCarrierColor_boundaryStep_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredCarrierColor n (fkIsingSquareWiredBoundaryStep n hn omega x) = fkIsingSquareWiredCarrierColor n x := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCarrierColor_boundaryStep n hn omega x

/--
[fkIsingSquareWiredCompletedLoopGraph_adj_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_adj_iff_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj x y ↔ y = fkIsingSquareWiredTransitionEquiv n hn omega x ∨ y = fkIsingSquareWiredCompletedIncidenceEquiv n x := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_adj_iff n hn omega x y

/--
[fkIsingSquareWiredCompletedLoopGraph_adj_color_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredCompletedLoopGraph_adj_color_ne_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Adj x y) :
-- imply
  fkIsingSquareWiredCarrierColor n x ≠ fkIsingSquareWiredCarrierColor n y := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredCompletedLoopGraph_adj_color_ne n hn omega hxy

/--
[fkIsingSquareWiredBoundaryStep_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredBoundaryStep_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x : FKIsingSquareWiredCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x (fkIsingSquareWiredBoundaryStep n hn omega x) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBoundaryStep_reachable n hn omega x

/--
[fkIsingSquareWired_reachable_of_blackBoundary_sameCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWired_reachable_of_blackBoundary_sameCycle_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredBlackCarrier n}
-- given
  (hn : 0 < n)
  (hxy : (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle x y) :
-- imply
  (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x.1 y.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_reachable_of_blackBoundary_sameCycle n hn omega x y hxy

/--
[fkIsingSquareWired_blackBoundary_sameCycle_of_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWired_blackBoundary_sameCycle_of_walk_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredCarrier n}
  {p : (fkIsingSquareWiredCompletedLoopGraph n hn omega).Walk x y}
-- given
  (hn : 0 < n)
  (hx : fkIsingSquareWiredCarrierColor n x = false)
  (hy : fkIsingSquareWiredCarrierColor n y = false) :
-- imply
  (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle ⟨x, hx⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_blackBoundary_sameCycle_of_walk n hn omega p hx hy

/--
[fkIsingSquareWired_blackBoundary_sameCycle_iff_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWired_blackBoundary_sameCycle_iff_reachable_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {x y : FKIsingSquareWiredBlackCarrier n}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredBlackBoundaryPerm n hn omega).SameCycle x y ↔ (fkIsingSquareWiredCompletedLoopGraph n hn omega).Reachable x.1 y.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareWired_blackBoundary_sameCycle_iff_reachable n hn omega x y

/--
[fkIsingSquareWiredBlackBoundaryCycleToComponent_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredBlackBoundaryCycleToComponent_bijective_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  Function.Bijective (fkIsingSquareWiredBlackBoundaryCycleToComponent n hn omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBlackBoundaryCycleToComponent_bijective n hn omega

/--
[permCycleCount_fkIsingSquareWiredBlackBoundaryPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma permCycleCount_fkIsingSquareWiredBlackBoundaryPerm_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
-- given
  (hn : 0 < n) :
-- imply
  StatMech.FrontierA.permCycleCount (fkIsingSquareWiredBlackBoundaryPerm n hn omega) = Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn omega).ConnectedComponent := by
-- proof
  apply StatMech.Universality.permCycleCount_fkIsingSquareWiredBlackBoundaryPerm n hn omega

/--
[fkIsingSquareWiredBlackWest_ne_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredBlackWest_ne_east_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareWiredBlackWest n e ≠ fkIsingSquareWiredBlackEast n e := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBlackWest_ne_east n e

/--
[fkIsingSquareWiredBlackLocalSwap_isSwap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredBlackLocalSwap_isSwap_eq
  {n : Nat}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)} :
-- imply
  (fkIsingSquareWiredBlackLocalSwap n e).IsSwap := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBlackLocalSwap_isSwap n e

/--
[fkIsingSquareWiredBlackLocalSwap_apply_of_edge_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredBlackLocalSwap_apply_of_edge_ne_eq
  {n : Nat}
  {e f : FKIsingMedialVertex (fkSquareBoxPlanar n)}
  {x : FKIsingSquareWiredBlackCarrier n}
-- given
  (hef : e ≠ f)
  (hx : x.1 = .dart (f, .west) ∨ x.1 = .dart (f, .east)) :
-- imply
  fkIsingSquareWiredBlackLocalSwap n e x = x := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBlackLocalSwap_apply_of_edge_ne n hef x hx

/--
[fkIsingSquareWiredBlackLocalSwap_commute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredBlackLocalSwap_commute_eq
  {n : Nat}
  {e f : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hef : e ≠ f) :
-- imply
  Commute (fkIsingSquareWiredBlackLocalSwap n e) (fkIsingSquareWiredBlackLocalSwap n f) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBlackLocalSwap_commute n hef

/--
[fkIsingSquareWiredBlackBoundaryPerm_setOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredBlackBoundaryPerm_setOpen_eq
  {n : Nat}
  {omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V)}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (hn : 0 < n) :
-- imply
  fkIsingSquareWiredBlackBoundaryPerm n hn (setOpen e.1 omega) = fkIsingSquareWiredBlackBoundaryPerm n hn (setClosed e.1 omega) * fkIsingSquareWiredBlackLocalSwap n e := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredBlackBoundaryPerm_setOpen n hn omega e

/--
[fkIsingSquareWiredConfigurationOfEdges_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredConfigurationOfEdges_apply_eq
  {n : Nat}
  {F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n))}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)} :
-- imply
  fkIsingSquareWiredConfigurationOfEdges n F e.1 = true ↔ e ∈ F := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredConfigurationOfEdges_apply n F e

/--
[fkIsingSquareWiredConfigurationOfEdges_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredConfigurationOfEdges_insert_eq
  {n : Nat}
  {F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n))}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (he : e ∉ F) :
-- imply
  fkIsingSquareWiredConfigurationOfEdges n (insert e F) = setOpen e.1 (fkIsingSquareWiredConfigurationOfEdges n F) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredConfigurationOfEdges_insert n F e he

/--
[fkIsingSquareWiredConfigurationOfEdges_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredConfigurationOfEdges_closed_eq
  {n : Nat}
  {F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n))}
  {e : FKIsingMedialVertex (fkSquareBoxPlanar n)}
-- given
  (he : e ∉ F) :
-- imply
  setClosed e.1 (fkIsingSquareWiredConfigurationOfEdges n F) = fkIsingSquareWiredConfigurationOfEdges n F := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredConfigurationOfEdges_closed n F e he

/--
[fkIsingSquareWiredRibbonSystem_boundaryPerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredRibbonSystem_boundaryPerm_eq
  {n : Nat}
  {F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n))}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredRibbonSystem n hn).boundaryPerm F = fkIsingSquareWiredBlackBoundaryPerm n hn (fkIsingSquareWiredConfigurationOfEdges n F) := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRibbonSystem_boundaryPerm n hn F

/--
[fkIsingSquareWiredRibbonSystem_boundaryComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredRibbon.lean)
-/
@[path]
private lemma fkIsingSquareWiredRibbonSystem_boundaryComponents_eq
  {n : Nat}
  {F : Finset (FKIsingMedialVertex (fkSquareBoxPlanar n))}
-- given
  (hn : 0 < n) :
-- imply
  (fkIsingSquareWiredRibbonSystem n hn).boundaryComponents F = Nat.card (fkIsingSquareWiredCompletedLoopGraph n hn (fkIsingSquareWiredConfigurationOfEdges n F)).ConnectedComponent := by
-- proof
  apply StatMech.Universality.fkIsingSquareWiredRibbonSystem_boundaryComponents n hn F


-- created on 2026-10-23
