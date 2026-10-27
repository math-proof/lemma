import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderPlanarization.Part8
open Finset SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectHorizontalCylinderGraph_not_crossesVerticalSeam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderGraph_not_crossesVerticalSeam_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
-- given
  (hxy : (fkRectHorizontalCylinderGraph R).Adj x y) :
-- imply
  ¬ fkRectCrossesVerticalSeam R s(x, y) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderGraph_not_crossesVerticalSeam R hxy

/--
[fkRectHorizontalCylinderWalk_winding_snd_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderWalk_winding_snd_eq_zero_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
  {p : (fkRectHorizontalCylinderGraph R).Walk x y} :
-- imply
  (fkRectWalkWinding R p).2 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderWalk_winding_snd_eq_zero R p

/--
[fkRectHorizontalCylinder_support_intersects_bottomTop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_support_intersects_bottomTop_eq
  {R : FKRectTorus}
  {bottomX topX : Fin R.width}
  {V : (fkRectHorizontalCylinderGraph R).Walk (bottomX, fkRectBottomRow R) (topX, fkRectTopRow R)}
  {x : R.Vertex}
  {W : (fkRectHorizontalCylinderGraph R).Walk x x}
-- given
  (hwind : (fkRectWalkWinding R W).1 ≠ 0) :
-- imply
  ∃ v, v ∈ W.support ∧ v ∈ V.support := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_support_intersects_bottomTop R bottomX topX V W hwind

/--
[fkRectHorizontalCylinder_crosscutSeparates_of_crossingRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_crosscutSeparates_of_crossingRoot_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {bottomX : Fin R.width}
-- given
  (hbottomS : bottomX ∈ S)
  (hcross : FKRectHorizontalCylinderCrossingSource R rho bottomX) :
-- imply
  FKRectHorizontalCylinderCrosscutSeparatesHorizontalWinding R rho S := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_crosscutSeparates_of_crossingRoot R rho S hbottomS hcross

/--
[fkRectHorizontalCylinder_crosscutSeparates_of_pairedWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_crosscutSeparates_of_pairedWitness_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {pair : Fin R.width → Fin R.width}
  {S : Finset (Fin R.width)}
-- given
  (hS : S.Nonempty)
  (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair S rho) :
-- imply
  FKRectHorizontalCylinderCrosscutSeparatesHorizontalWinding R rho S := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_crosscutSeparates_of_pairedWitness R rho pair S hS hW

/--
[fkRectHorizontalCylinderUnexploredWalk_winding_snd_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderUnexploredWalk_winding_snd_eq_zero_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {x y}
  {p : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)).Walk x y} :
-- imply
  (fkRectHorizontalCylinderUnexploredWalkWinding R rho S p).2 = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderUnexploredWalk_winding_snd_eq_zero R rho S p

/--
[fkRectHorizontalCylinder_noHorizontalWinding_of_crosscutSeparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_noHorizontalWinding_of_crosscutSeparation_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
-- given
  (hsep : FKRectHorizontalCylinderCrosscutSeparatesHorizontalWinding R rho S) :
-- imply
  FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_noHorizontalWinding_of_crosscutSeparation R rho S hsep

/--
[fkRectHorizontalCylinder_noHorizontalWinding_of_pairedWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_noHorizontalWinding_of_pairedWitness_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {pair : Fin R.width → Fin R.width}
  {S : Finset (Fin R.width)}
-- given
  (hS : S.Nonempty)
  (hW : FKRectHorizontalCylinderDistinctPairedWitness R pair S rho) :
-- imply
  FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_noHorizontalWinding_of_pairedWitness R rho pair S hS hW

/--
[fkRectHorizontalCylinderUnexploredComponentRoot_component](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderUnexploredComponentRoot_component_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {x : FKRectHorizontalCylinderUnexploredVertex R rho S} :
-- imply
  (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)).connectedComponentMk (fkRectHorizontalCylinderUnexploredComponentRoot R rho S x) = (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)).connectedComponentMk x := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderUnexploredComponentRoot_component R rho S x

/--
[fkRectHorizontalCylinderUnexploredLiftPoint_project](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderUnexploredLiftPoint_project_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {x : FKRectHorizontalCylinderUnexploredVertex R rho S} :
-- imply
  fkRectLiftedVertex R (fkRectHorizontalCylinderUnexploredLiftPoint R rho S x) = x.1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderUnexploredLiftPoint_project R rho S x

/--
[fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {x : FKRectHorizontalCylinderUnexploredVertex R rho S} :
-- imply
  (fkRectHorizontalCylinderUnexploredLiftPoint R rho S x).2 = (x.1.2.val : Int) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderUnexploredLiftPoint_snd_eq_val R rho S x

/--
[fkRectHorizontalCylinderUnexploredLiftSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderUnexploredLiftSite_injective_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)} :
-- imply
  Function.Injective (fkRectHorizontalCylinderUnexploredLiftSite R rho S) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderUnexploredLiftSite_injective R rho S

/--
[fkRectHorizontalCylinderUnexploredLiftSite_adj_of_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderUnexploredLiftSite_adj_of_adj_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {x y : FKRectHorizontalCylinderUnexploredVertex R rho S}
-- given
  (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S)
  (hxy : (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)).Adj x y) :
-- imply
  (hypercubicLattice 2).Adj (fkRectHorizontalCylinderUnexploredLiftSite R rho S x) (fkRectHorizontalCylinderUnexploredLiftSite R rho S y) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderUnexploredLiftSite_adj_of_adj R rho S hno hxy

/--
[fkRectHorizontalCylinderUnexploredBoxEmbedding_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderUnexploredBoxEmbedding_injective_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)} :
-- imply
  Function.Injective (fkRectHorizontalCylinderUnexploredBoxEmbedding R rho S) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderUnexploredBoxEmbedding_injective R rho S

/--
[fkRectHorizontalCylinderUnexploredBox_adjMatch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderUnexploredBox_adjMatch_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
-- given
  (hno : FKRectHorizontalCylinderUnexploredNoHorizontalWinding R rho S) :
-- imply
  FK.ocd_AdjMatch (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) (FK.boxGraph 2 (fkRectHorizontalCylinderUnexploredLiftRadius R rho S)) (fkRectHorizontalCylinderUnexploredBoxEmbedding R rho S) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderUnexploredBox_adjMatch R rho S hno

/--
[fkRectHorizontalCylinderUnexploredConnection_freeMass_le_boxConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinderUnexploredConnection_freeMass_le_boxConn_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {P : FKRectHorizontalCylinderUnexploredPlanarization R rho S}
  {source target : FKRectHorizontalCylinderUnexploredVertex R rho S}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (∑ omega, (FKFiniteConnectionEvent (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) source target).indicator (fun _ => (1 : Real)) omega * FK.fkProb (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) p q omega) ≤ (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxConnEvent 2 P.radius (P.embedding source) (P.embedding target)) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinderUnexploredConnection_freeMass_le_boxConn R rho S P source target hp hp1 hq

/--
[fkRectHorizontalCylinder_conditionalConnection_le_boxConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_conditionalConnection_le_boxConn_eq
  {R : FKRectTorus}
  {rho : ConfigSpace (Sym2 R.Vertex)}
  {S : Finset (Fin R.width)}
  {P : FKRectHorizontalCylinderUnexploredPlanarization R rho S}
  {source target : FKRectHorizontalCylinderUnexploredVertex R rho S}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (∑ sigma : ConfigSpace (Sym2 R.Vertex), (FK.ocd_innerRestrict (Subtype.val : FKRectHorizontalCylinderUnexploredVertex R rho S → R.Vertex) ⁻¹' FKFiniteConnectionEvent (FK.clusterUnexploredGraph (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) source target).indicator (fun _ => (1 : Real)) sigma * FK.condBcProb (fkRectHorizontalCylinderGraph R) (StatMech.Lattice.boundaryCliqueGraph (fun _ : R.Vertex => False)) p q (FK.clusterUnexploredPairEdges (fkRectHorizontalCylinderGraph R) rho (fkRectHorizontalCylinderBottomRoots R S)) rho sigma) ≤ (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) : MeasureTheory.Measure (ConfigSpace (Sym2 (StatMech.Lattice.Site 2)))).real (FK.boxConnEvent 2 P.radius (P.embedding source) (P.embedding target)) := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_conditionalConnection_le_boxConn R rho S P source target hp hp1 hq

/--
[fkRectHorizontalCylinder_bottom_top_verticalDisplacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderPlanarization.lean)
-/
@[path]
private lemma fkRectHorizontalCylinder_bottom_top_verticalDisplacement_eq
  {R : FKRectTorus}
  {x y : Fin R.width} :
-- imply
  ((y, fkRectTopRow R).2.val : Int) - ((x, fkRectBottomRow R).2.val : Int) = R.height - 1 := by
-- proof
  apply StatMech.FrontierD.fkRectHorizontalCylinder_bottom_top_verticalDisplacement R x y


-- created on 2026-10-23
