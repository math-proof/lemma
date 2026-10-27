import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryIncidenceConnected.Part2
open Equiv Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkMedialBlackDart_pair_eq_dart01_of_base_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkMedialBlackDart_pair_eq_dart01_of_base_eq_eq
  {T : EvenTorus}
  {v : T.Vertex}
  {d e : FKMedialBlackDart T}
-- given
  (hd : d.1.1 = v)
  (he : e.1.1 = v)
  (hne : d ≠ e) :
-- imply
  s(d, e) = s(fkMedialBlackDart0 v, fkMedialBlackDart1 v) := by
-- proof
  apply StatMech.FrontierD.fkMedialBlackDart_pair_eq_dart01_of_base_eq v d e hd he hne

/--
[fkMedialLocalMate_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkMedialLocalMate_fst_eq
  {T : EvenTorus}
  {pairing : FKMedialLoopPairing T}
  {d : FKMedialDart T} :
-- imply
  (fkMedialLocalMate pairing d).1 = d.1 := by
-- proof
  apply StatMech.FrontierD.fkMedialLocalMate_fst pairing d

/--
[fkRectDualBlackDartEquiv_localPair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkRectDualBlackDartEquiv_localPair_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {v : R.medialTorus.Vertex} :
-- imply
  s(fkRectDualBlackDartEquiv R omega (fkMedialBlackDart0 v), fkRectDualBlackDartEquiv R omega (fkMedialBlackDart1 v)) = s(fkMedialBlackDart0 (fkRectMedialDualShiftVertex R v), fkMedialBlackDart1 (fkRectMedialDualShiftVertex R v)) := by
-- proof
  apply StatMech.FrontierD.fkRectDualBlackDartEquiv_localPair R omega v

/--
[fkRectBoundaryLocalPair_left_eq_of_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkRectBoundaryLocalPair_left_eq_of_open_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex}
-- given
  (hopen : omega e = true) :
-- imply
  fkRectBlackBoundaryCyclePrimalComponent R omega (Quot.mk _ (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))) = fkRectBlackBoundaryCyclePrimalComponent R omega (Quot.mk _ (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLocalPair_left_eq_of_open R omega e hopen

/--
[fkRectBoundaryLocalPair_right_eq_of_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkRectBoundaryLocalPair_right_eq_of_closed_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex}
-- given
  (hclosed : omega e = false) :
-- imply
  fkRectBlackBoundaryCycleDualComponent R omega (Quot.mk _ (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))) = fkRectBlackBoundaryCycleDualComponent R omega (Quot.mk _ (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLocalPair_right_eq_of_closed R omega e hclosed

/--
[fkRectBoundaryLocalPair_incidence_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkRectBoundaryLocalPair_incidence_reachable_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex} :
-- imply
  let left := fkRectBlackBoundaryCyclePrimalComponent R omega let right := fkRectBlackBoundaryCycleDualComponent R omega (bipartiteEdgeIncidenceGraph left right).Reachable (Quot.mk _ (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))) (Quot.mk _ (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e))) := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryLocalPair_incidence_reachable R omega e

/--
[fkRectBlackBoundaryCyclePrimalComponent_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCyclePrimalComponent_surjective_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Function.Surjective (fkRectBlackBoundaryCyclePrimalComponent R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCyclePrimalComponent_surjective R omega

/--
[bipartiteEdgeIncidenceGraph_reachable_of_label_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma bipartiteEdgeIncidenceGraph_reachable_of_label_eq_eq
  {left : E → P}
  {right : E → D}
  {C D' : E}
-- given
  (h : left C = left D' ∨ right C = right D') :
-- imply
  (bipartiteEdgeIncidenceGraph left right).Reachable C D' := by
-- proof
  apply StatMech.FrontierD.bipartiteEdgeIncidenceGraph_reachable_of_label_eq left right h

/--
[fkRectBoundaryIncidence_reachable_of_torus_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkRectBoundaryIncidence_reachable_of_torus_adj_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {C D : FKRectConfigurationBlackBoundaryCycle R omega}
-- given
  (hxy : (fkRectTorusGraph R).Adj x y)
  (hC : fkRectBlackBoundaryCyclePrimalComponent R omega C = (fkRectOpenGraph R omega).connectedComponentMk x)
  (hD : fkRectBlackBoundaryCyclePrimalComponent R omega D = (fkRectOpenGraph R omega).connectedComponentMk y) :
-- imply
  let left := fkRectBlackBoundaryCyclePrimalComponent R omega let right := fkRectBlackBoundaryCycleDualComponent R omega (bipartiteEdgeIncidenceGraph left right).Reachable C D := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryIncidence_reachable_of_torus_adj R omega hxy C D hC hD

/--
[fkRectBoundaryIncidence_reachable_of_torus_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkRectBoundaryIncidence_reachable_of_torus_walk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
  {p : (fkRectTorusGraph R).Walk x y}
  {C D : FKRectConfigurationBlackBoundaryCycle R omega}
-- given
  (hC : fkRectBlackBoundaryCyclePrimalComponent R omega C = (fkRectOpenGraph R omega).connectedComponentMk x)
  (hD : fkRectBlackBoundaryCyclePrimalComponent R omega D = (fkRectOpenGraph R omega).connectedComponentMk y) :
-- imply
  let left := fkRectBlackBoundaryCyclePrimalComponent R omega let right := fkRectBlackBoundaryCycleDualComponent R omega (bipartiteEdgeIncidenceGraph left right).Reachable C D := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryIncidence_reachable_of_torus_walk R omega p C D hC hD

/--
[fkRectBoundaryCycleIncidence_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkRectBoundaryCycleIncidence_connected_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  (bipartiteEdgeIncidenceGraph (fkRectBlackBoundaryCyclePrimalComponent R omega) (fkRectBlackBoundaryCycleDualComponent R omega)).Connected := by
-- proof
  apply StatMech.FrontierD.fkRectBoundaryCycleIncidence_connected R omega

/--
[fkRectBlackBoundaryCycleDualComponent_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkRectBlackBoundaryCycleDualComponent_surjective_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Function.Surjective (fkRectBlackBoundaryCycleDualComponent R omega) := by
-- proof
  apply StatMech.FrontierD.fkRectBlackBoundaryCycleDualComponent_surjective R omega

/--
[card_fkRectConfigurationBlackBoundaryCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma card_fkRectConfigurationBlackBoundaryCycle_eq
  {R : FKRectTorus}
  {omega : R.Configuration} :
-- imply
  Fintype.card (FKRectConfigurationBlackBoundaryCycle R omega) = fkRectMedialLoopCount R omega := by
-- proof
  apply StatMech.FrontierD.card_fkRectConfigurationBlackBoundaryCycle R omega

/--
[card_boundaryCycles_le_incidentComponents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma card_boundaryCycles_le_incidentComponents_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  [DecidableEq (fkRectOpenGraph R omega).ConnectedComponent]
  [DecidableEq (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).ConnectedComponent] :
-- imply
  Fintype.card (FKRectConfigurationBlackBoundaryCycle R omega) ≤ ((Finset.univ : Finset (FKRectConfigurationBlackBoundaryCycle R omega)).image (fkRectBlackBoundaryCyclePrimalComponent R omega)).card + ((Finset.univ : Finset (FKRectConfigurationBlackBoundaryCycle R omega)).image (fkRectBlackBoundaryCycleDualComponent R omega)).card := by
-- proof
  apply StatMech.FrontierD.card_boundaryCycles_le_incidentComponents R omega

/--
[card_boundaryCycles_le_incidentComponents_of_not_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma card_boundaryCycles_le_incidentComponents_of_not_hasNet_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  [DecidableEq (fkRectOpenGraph R omega).ConnectedComponent]
  [DecidableEq (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).ConnectedComponent]
-- given
  (_hnoNet : ¬ FKRectHasNet R omega) :
-- imply
  Fintype.card (FKRectConfigurationBlackBoundaryCycle R omega) ≤ ((Finset.univ : Finset (FKRectConfigurationBlackBoundaryCycle R omega)).image (fkRectBlackBoundaryCyclePrimalComponent R omega)).card + ((Finset.univ : Finset (FKRectConfigurationBlackBoundaryCycle R omega)).image (fkRectBlackBoundaryCycleDualComponent R omega)).card := by
-- proof
  apply StatMech.FrontierD.card_boundaryCycles_le_incidentComponents_of_not_hasNet R omega _hnoNet

/--
[fkRectPrimalBoundarySupportedFiberSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkRectPrimalBoundarySupportedFiberSum_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
  [DecidableEq (fkRectOpenGraph R omega).ConnectedComponent] :
-- imply
  (∑ C ∈ ((Finset.univ : Finset (FKRectConfigurationBlackBoundaryCycle R omega)).filter fun C ↦ fkRectBlackBoundaryCycleWinding R omega C ≠ 0).filter (fun C ↦ fkRectBlackBoundaryCyclePrimalComponent R omega C = K), fkRectBlackBoundaryCycleWinding R omega C) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectPrimalBoundarySupportedFiberSum_eq_zero R omega K

/--
[fkRectDualBoundarySupportedFiberSum_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma fkRectDualBoundarySupportedFiberSum_eq_zero_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {L : (fkRectOpenGraph R (fkRectDualConfigurationEquiv R omega)).ConnectedComponent} :
-- imply
  fkRectDualBoundarySupportedFiberSum R omega L = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectDualBoundarySupportedFiberSum_eq_zero R omega L

/--
[card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent} :
-- imply
  (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2 := by
-- proof
  apply StatMech.FrontierD.card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two R omega K

/--
[card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_atVertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_atVertex_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x : R.Vertex} :
-- imply
  (fkRectPrimalClusterNonzeroBoundaryCycles R omega x).card ≤ 2 := by
-- proof
  apply StatMech.FrontierD.card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_atVertex R omega x

/--
[card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_not_hasNet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryIncidenceConnected.lean)
-/
@[path]
private lemma card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_not_hasNet_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {K : (fkRectOpenGraph R omega).ConnectedComponent}
-- given
  (_hnoNet : ¬ FKRectHasNet R omega) :
-- imply
  (fkRectPrimalClusterNonzeroBoundaryCycles R omega K.out).card ≤ 2 := by
-- proof
  apply StatMech.FrontierD.card_fkRectPrimalClusterNonzeroBoundaryCycles_le_two_of_not_hasNet R omega _hnoNet K


-- created on 2026-10-23
