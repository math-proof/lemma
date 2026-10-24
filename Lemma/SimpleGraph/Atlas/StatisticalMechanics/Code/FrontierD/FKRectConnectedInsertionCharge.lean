import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectConnectedInsertionCharge
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectTorusIndexedEdge_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectTorusIndexedEdge_injective_eq
  {R : FKRectTorus} :
-- imply
  Function.Injective (fkRectTorusIndexedEdge R) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusIndexedEdge_injective R

/--
[fkRectInsertedEdgeCharge_eq_zero_of_oldWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectInsertedEdgeCharge_eq_zero_of_oldWalk_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {x y : R.Vertex}
  {p : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk x y}
-- given
  (heF : e ∉ F) :
-- imply
  fkRectInsertedEdgeCharge R e p = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedEdgeCharge_eq_zero_of_oldWalk R F e heF p

/--
[fkRectWalkWinding_insert_eq_old_add_charge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectWalkWinding_insert_eq_old_add_charge_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {u v : R.Vertex}
  {p : (fkRectOpenGraph R (fkRectConfigurationOfEdges R (insert e F))).Walk u v}
-- given
  (heF : e ∉ F) :
-- imply
  ∃ q : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk u v, fkRectWalkWinding R p = fkRectWalkWinding R q + fkRectInsertedEdgeCharge R e p • fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r) := by
-- proof
  apply StatMech.FrontierD.fkRectWalkWinding_insert_eq_old_add_charge R F e r heF p

/--
[fkRectMedialBoundaryStep_label_eq_or_indexedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectMedialBoundaryStep_label_eq_or_indexedEdge_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectMedialDartPrimalLabel R d = fkRectMedialDartPrimalLabel R (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega) d) ∨ fkRectTorusIndexedEdge R (fkRectTorusMedialEdgeEquiv R d.1) = s(fkRectMedialDartPrimalLabel R d, fkRectMedialDartPrimalLabel R (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega) d)) := by
-- proof
  apply StatMech.FrontierD.fkRectMedialBoundaryStep_label_eq_or_indexedEdge R omega d

/--
[fkRectInsertedEdgeCharge_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectInsertedEdgeCharge_append_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex}
  {G : SimpleGraph R.Vertex}
  {x y z : R.Vertex}
  {p : G.Walk x y}
  {q : G.Walk y z} :
-- imply
  fkRectInsertedEdgeCharge R e (p.append q) = fkRectInsertedEdgeCharge R e p + fkRectInsertedEdgeCharge R e q := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedEdgeCharge_append R e p q

/--
[fkRectInsertedEdgeCharge_copy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectInsertedEdgeCharge_copy_eq
  {R : FKRectTorus}
  {e : R.EdgeIndex}
  {G : SimpleGraph R.Vertex}
  {x y x' y' : R.Vertex}
  {p : G.Walk x y}
-- given
  (hx : x = x')
  (hy : y = y') :
-- imply
  fkRectInsertedEdgeCharge R e (p.copy hx hy) = fkRectInsertedEdgeCharge R e p := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedEdgeCharge_copy R e p hx hy

/--
[fkRectInsertedEdgeCharge_boundaryStepWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectInsertedEdgeCharge_boundaryStepWalk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectInsertedEdgeCharge R e (fkRectMedialBoundaryPrimalStepWalk R omega d) = fkRectInsertedEdgeStepCharge R e (fkRectMedialDartPrimalLabel R d) (fkRectMedialDartPrimalLabel R (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega) d)) := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedEdgeCharge_boundaryStepWalk R omega e d

/--
[fkRectInsertedEdgeCharge_boundaryTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectInsertedEdgeCharge_boundaryTrace_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus}
  {n : Nat} :
-- imply
  fkRectInsertedEdgeCharge R e (fkRectMedialBoundaryPrimalTrace R omega d n) = ∑ i ∈ Finset.range n, fkRectInsertedEdgeStepCharge R e (fkRectMedialDartPrimalLabel R ((fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))^[i] d)) (fkRectMedialDartPrimalLabel R ((fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))^[i + 1] d)) := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedEdgeCharge_boundaryTrace R omega e d n

/--
[fkRectInsertedEdgeCharge_boundaryOrbitWalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectInsertedEdgeCharge_boundaryOrbitWalk_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex}
  {d : FKMedialDart R.medialTorus} :
-- imply
  fkRectInsertedEdgeCharge R e (fkRectMedialBoundaryPrimalOrbitWalk R omega d) = ∑ i ∈ Finset.range (orderOf (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))), fkRectInsertedEdgeStepCharge R e (fkRectMedialDartPrimalLabel R ((fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))^[i] d)) (fkRectMedialDartPrimalLabel R ((fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega))^[i + 1] d)) := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedEdgeCharge_boundaryOrbitWalk R omega e d

/--
[fkRectInsertedEdgeStepCharge_black_eq_zero_of_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectInsertedEdgeStepCharge_black_eq_zero_of_ne_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {e : R.EdgeIndex}
  {d : FKMedialBlackDart R.medialTorus}
-- given
  (hd0 : d ≠ fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e))
  (hd1 : d ≠ fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) :
-- imply
  fkRectInsertedEdgeStepCharge R e (fkRectMedialDartPrimalLabel R d.1) (fkRectMedialDartPrimalLabel R (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R omega) d.1)) = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedEdgeStepCharge_black_eq_zero_of_ne R omega e d hd0 hd1

/--
[fkRectInsertedEdgeStepCharge_new_dart0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectInsertedEdgeStepCharge_new_dart0_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex} :
-- imply
  fkRectInsertedEdgeStepCharge R e (fkRectMedialDartPrimalLabel R (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1) (fkRectMedialDartPrimalLabel R (fkMedialBoundaryStep (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R (insert e F))) (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1)) = if fkMedialVertexParity (fkRectMedialVertexOfEdge R e) then 1 else -1 := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedEdgeStepCharge_new_dart0 R F e

/--
[fkRectInsertedEdgeCharge_newBoundaryOrbit_ne_zero_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectInsertedEdgeCharge_newBoundaryOrbit_ne_zero_of_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
-- given
  (heF : e ∉ F)
  (hreach : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  fkRectInsertedEdgeCharge R e (fkRectMedialBoundaryPrimalOrbitWalk R (fkRectConfigurationOfEdges R (insert e F)) (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)).1) ≠ 0 := by
-- proof
  apply StatMech.FrontierD.fkRectInsertedEdgeCharge_newBoundaryOrbit_ne_zero_of_reachable R F e heF hreach

/--
[fkRectConnectedInsertion_not_independent_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectConnectedInsertion_not_independent_of_reachable_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
  {q : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e)}
-- given
  (heF : e ∉ F)
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F))
  (hreach : (fkMedialLoopGraph R.medialTorus (fkRectConfigurationToMedialPairing R (fkRectConfigurationOfEdges R F))).Reachable (fkMedialWestDart (fkRectMedialVertexOfEdge R e)) (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) :
-- imply
  ¬ FKRectWindingIndependent (fkRectWalkWinding R q) (fkRectWalkWinding R (fkRectInsertedFundamentalWalk R F e r)) := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertion_not_independent_of_reachable R F e r heF hold hreach q

/--
[fkRectConnectedInsertionSurfaceBridge_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectConnectedInsertionCharge.lean)
-/
@[path]
private lemma fkRectConnectedInsertionSurfaceBridge_unconditional_eq
  {R : FKRectTorus}
  {F : Finset R.EdgeIndex}
  {e : R.EdgeIndex}
  {r : (fkRectOpenGraph R (fkRectConfigurationOfEdges R F)).Walk (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e)}
-- given
  (heF : e ∉ F)
  (hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F)) :
-- imply
  FKRectConnectedInsertionSurfaceBridge R F e r heF hold := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedInsertionSurfaceBridge_unconditional R F e r heF hold


-- created on 2026-10-23
