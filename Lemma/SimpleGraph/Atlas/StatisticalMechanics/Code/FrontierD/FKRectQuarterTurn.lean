import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part9
open Set SimpleGraph StatMech.Lattice StatMech StatMech.FrontierD


/--
[fkRectQuarterTurnTorus_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectQuarterTurnTorus_width_eq
  {R : FKRectTorus}
-- given
  (hheight : 4 < R.height) :
-- imply
  (fkRectQuarterTurnTorus R hheight).width = R.height / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnTorus_width R hheight

/--
[fkRectQuarterTurnTorus_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectQuarterTurnTorus_height_eq
  {R : FKRectTorus}
-- given
  (hheight : 4 < R.height) :
-- imply
  (fkRectQuarterTurnTorus R hheight).height = 2 * R.width := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnTorus_height R hheight

/--
[fkRectQuarterTurnVertex_fst_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectQuarterTurnVertex_fst_val_eq
  {R : FKRectTorus}
  {v : R.Vertex}
-- given
  (hheight : 4 < R.height) :
-- imply
  (fkRectQuarterTurnVertex R hheight v).1.val = v.2.val / 2 := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnVertex_fst_val R hheight v

/--
[fkRectQuarterTurnVertex_snd_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectQuarterTurnVertex_snd_val_eq
  {R : FKRectTorus}
  {v : R.Vertex}
-- given
  (hheight : 4 < R.height) :
-- imply
  (fkRectQuarterTurnVertex R hheight v).2.val = 2 * v.1.val + v.2.val % 2 := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnVertex_snd_val R hheight v

/--
[fkRectQuarterTurnVertexInv_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectQuarterTurnVertexInv_left_eq
  {R : FKRectTorus}
  {v : R.Vertex}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectQuarterTurnVertexInv R hheight (fkRectQuarterTurnVertex R hheight v) = v := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnVertexInv_left R hheight v

/--
[fkRectQuarterTurnVertexInv_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectQuarterTurnVertexInv_right_eq
  {R : FKRectTorus}
  {v : (fkRectQuarterTurnTorus R hheight).Vertex}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectQuarterTurnVertex R hheight (fkRectQuarterTurnVertexInv R hheight v) = v := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnVertexInv_right R hheight v

/--
[fkRectQuarterTurnVertexEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectQuarterTurnVertexEquiv_apply_eq
  {R : FKRectTorus}
  {v : R.Vertex}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectQuarterTurnVertexEquiv R hheight v = fkRectQuarterTurnVertex R hheight v := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnVertexEquiv_apply R hheight v

/--
[fkRectQuarterTurnEdgeInv_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectQuarterTurnEdgeInv_left_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectQuarterTurnEdgeInv R hheight (fkRectQuarterTurnEdge R hheight a) = a := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnEdgeInv_left R hheight a

/--
[fkRectQuarterTurnEdgeInv_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectQuarterTurnEdgeInv_right_eq
  {R : FKRectTorus}
  {a : (fkRectQuarterTurnTorus R hheight).EdgeIndex}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectQuarterTurnEdge R hheight (fkRectQuarterTurnEdgeInv R hheight a) = a := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnEdgeInv_right R hheight a

/--
[fkRectQuarterTurnEdgeEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectQuarterTurnEdgeEquiv_apply_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectQuarterTurnEdgeEquiv R hheight a = fkRectQuarterTurnEdge R hheight a := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnEdgeEquiv_apply R hheight a

/--
[fkRectTorusIndexedEdge_quarterTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectTorusIndexedEdge_quarterTurn_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectTorusIndexedEdge (fkRectQuarterTurnTorus R hheight) (fkRectQuarterTurnEdgeEquiv R hheight a) = Sym2.map (fkRectQuarterTurnVertexEquiv R hheight) (fkRectTorusIndexedEdge R a) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusIndexedEdge_quarterTurn R hheight a

/--
[fkRectTorusGraph_adj_quarterTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectTorusGraph_adj_quarterTurn_eq
  {R : FKRectTorus}
  {x y : R.Vertex}
-- given
  (hheight : 4 < R.height) :
-- imply
  (fkRectTorusGraph (fkRectQuarterTurnTorus R hheight)).Adj (fkRectQuarterTurnVertexEquiv R hheight x) (fkRectQuarterTurnVertexEquiv R hheight y) ↔ (fkRectTorusGraph R).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectTorusGraph_adj_quarterTurn R hheight x y

/--
[fkRectQuarterTurnConfigurationEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectQuarterTurnConfigurationEquiv_apply_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {a : (fkRectQuarterTurnTorus R hheight).EdgeIndex}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectQuarterTurnConfigurationEquiv R hheight omega a = omega ((fkRectQuarterTurnEdgeEquiv R hheight).symm a) := by
-- proof
  apply StatMech.FrontierD.fkRectQuarterTurnConfigurationEquiv_apply R hheight omega a

/--
[fkRectOpenGraph_quarterTurn_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectOpenGraph_quarterTurn_adj_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex}
-- given
  (hheight : 4 < R.height) :
-- imply
  (fkRectOpenGraph (fkRectQuarterTurnTorus R hheight) (fkRectQuarterTurnConfigurationEquiv R hheight omega)).Adj (fkRectQuarterTurnVertexEquiv R hheight x) (fkRectQuarterTurnVertexEquiv R hheight y) ↔ (fkRectOpenGraph R omega).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_quarterTurn_adj R hheight omega x y

/--
[fkRectOpenEdgeCount_quarterTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectOpenEdgeCount_quarterTurn_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectOpenEdgeCount (fkRectQuarterTurnTorus R hheight) (fkRectQuarterTurnConfigurationEquiv R hheight omega) = fkRectOpenEdgeCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectOpenEdgeCount_quarterTurn R hheight omega

/--
[fkRectNumClusters_quarterTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectNumClusters_quarterTurn_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectNumClusters (fkRectQuarterTurnTorus R hheight) (fkRectQuarterTurnConfigurationEquiv R hheight omega) = fkRectNumClusters R omega := by
-- proof
  apply StatMech.FrontierD.fkRectNumClusters_quarterTurn R hheight omega

/--
[fkRectCriticalReducedWeight_quarterTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectCriticalReducedWeight_quarterTurn_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectCriticalReducedWeight (fkRectQuarterTurnTorus R hheight) q (fkRectQuarterTurnConfigurationEquiv R hheight omega) = fkRectCriticalReducedWeight R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedWeight_quarterTurn R hheight q omega

/--
[fkRectCriticalReducedZ_quarterTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectCriticalReducedZ_quarterTurn_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectCriticalReducedZ (fkRectQuarterTurnTorus R hheight) q = fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedZ_quarterTurn R hheight q

/--
[fkRectCriticalRandomClusterProb_quarterTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterProb_quarterTurn_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectCriticalRandomClusterProb (fkRectQuarterTurnTorus R hheight) q (fkRectQuarterTurnConfigurationEquiv R hheight omega) = fkRectCriticalRandomClusterProb R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterProb_quarterTurn R hheight q omega

/--
[fkRectCriticalEventMass_quarterTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_quarterTurn_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set (fkRectQuarterTurnTorus R hheight).Configuration}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectCriticalEventMass (fkRectQuarterTurnTorus R hheight) q A = fkRectCriticalEventMass R q ((fkRectQuarterTurnConfigurationEquiv R hheight) ⁻¹' A) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_quarterTurn R hheight q A

/--
[fkRectCriticalEventMass_quarterTurn_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_quarterTurn_image_eq
  {R : FKRectTorus}
  {q : Real}
  {A : Set R.Configuration}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectCriticalEventMass (fkRectQuarterTurnTorus R hheight) q (fkRectQuarterTurnConfigurationEquiv R hheight '' A) = fkRectCriticalEventMass R q A := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_quarterTurn_image R hheight q A

/--
[fkRectConnectedWithin_quarterTurn_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectConnectedWithin_quarterTurn_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {S : Set R.Vertex}
  {x y : S}
-- given
  (hheight : 4 < R.height) :
-- imply
  FKRectConnectedWithin (fkRectQuarterTurnTorus R hheight) (fkRectQuarterTurnConfigurationEquiv R hheight omega) (fkRectQuarterTurnSet R hheight S) (fkRectQuarterTurnSetEquiv R hheight S x) (fkRectQuarterTurnSetEquiv R hheight S y) ↔ FKRectConnectedWithin R omega S x y := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedWithin_quarterTurn_iff R hheight omega S x y

/--
[fkRectCritical_connectedWithinMass_quarterTurn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean)
-/
@[path]
private lemma fkRectCritical_connectedWithinMass_quarterTurn_eq
  {R : FKRectTorus}
  {q : Real}
  {S : Set R.Vertex}
  {x y : S}
-- given
  (hheight : 4 < R.height) :
-- imply
  fkRectCriticalEventMass (fkRectQuarterTurnTorus R hheight) q {omega | FKRectConnectedWithin (fkRectQuarterTurnTorus R hheight) omega (fkRectQuarterTurnSet R hheight S) (fkRectQuarterTurnSetEquiv R hheight S x) (fkRectQuarterTurnSetEquiv R hheight S y)} = fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega S x y} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_connectedWithinMass_quarterTurn R hheight q S x y


-- created on 2026-10-23
