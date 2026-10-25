import Mathlib
import sympy.Basic
import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part8
open Set SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectColumnTranslate_neg_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectColumnTranslate_neg_left_eq
  {R : FKRectTorus}
  {s : Int}
  {x : Fin R.width} :
-- imply
  fkRectColumnTranslate R (-s) (fkRectColumnTranslate R s x) = x := by
-- proof
  apply StatMech.FrontierD.fkRectColumnTranslate_neg_left R s x

/--
[fkRectColumnTranslate_neg_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectColumnTranslate_neg_right_eq
  {R : FKRectTorus}
  {s : Int}
  {x : Fin R.width} :
-- imply
  fkRectColumnTranslate R s (fkRectColumnTranslate R (-s) x) = x := by
-- proof
  apply StatMech.FrontierD.fkRectColumnTranslate_neg_right R s x

/--
[fkRectColumnTranslationEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectColumnTranslationEquiv_apply_eq
  {R : FKRectTorus}
  {s : Int}
  {x : Fin R.width} :
-- imply
  fkRectColumnTranslationEquiv R s x = fkRectColumnTranslate R s x := by
-- proof
  apply StatMech.FrontierD.fkRectColumnTranslationEquiv_apply R s x

/--
[fkRectColumnTranslate_cyclicPred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectColumnTranslate_cyclicPred_eq
  {R : FKRectTorus}
  {s : Int}
  {x : Fin R.width} :
-- imply
  fkRectColumnTranslate R s (SixVertexArrows.cyclicPred R.width_pos x) = SixVertexArrows.cyclicPred R.width_pos (fkRectColumnTranslate R s x) := by
-- proof
  apply StatMech.FrontierD.fkRectColumnTranslate_cyclicPred R s x

/--
[fkRectColumnTranslationVertexEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectColumnTranslationVertexEquiv_apply_eq
  {R : FKRectTorus}
  {s : Int}
  {v : R.Vertex} :
-- imply
  fkRectColumnTranslationVertexEquiv R s v = (fkRectColumnTranslate R s v.1, v.2) := by
-- proof
  apply StatMech.FrontierD.fkRectColumnTranslationVertexEquiv_apply R s v

/--
[fkRectColumnTranslationEdgeEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectColumnTranslationEdgeEquiv_apply_eq
  {R : FKRectTorus}
  {s : Int}
  {a : R.EdgeIndex} :
-- imply
  fkRectColumnTranslationEdgeEquiv R s a = (a.1, (fkRectColumnTranslate R s a.2.1, a.2.2)) := by
-- proof
  apply StatMech.FrontierD.fkRectColumnTranslationEdgeEquiv_apply R s a

/--
[fkRectTorusIndexedEdge_columnTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectTorusIndexedEdge_columnTranslation_eq
  {R : FKRectTorus}
  {s : Int}
  {a : R.EdgeIndex} :
-- imply
  fkRectTorusIndexedEdge R (fkRectColumnTranslationEdgeEquiv R s a) = Sym2.map (fkRectColumnTranslationVertexEquiv R s) (fkRectTorusIndexedEdge R a) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusIndexedEdge_columnTranslation R s a

/--
[fkRectColumnTranslationConfigurationEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectColumnTranslationConfigurationEquiv_apply_eq
  {R : FKRectTorus}
  {s : Int}
  {omega : R.Configuration}
  {a : R.EdgeIndex} :
-- imply
  fkRectColumnTranslationConfigurationEquiv R s omega a = omega ((fkRectColumnTranslationEdgeEquiv R s).symm a) := by
-- proof
  apply StatMech.FrontierD.fkRectColumnTranslationConfigurationEquiv_apply R s omega a

/--
[fkRectOpenGraph_columnTranslation_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectOpenGraph_columnTranslation_adj_eq
  {R : FKRectTorus}
  {s : Int}
  {omega : R.Configuration}
  {x y : R.Vertex} :
-- imply
  (fkRectOpenGraph R (fkRectColumnTranslationConfigurationEquiv R s omega)).Adj (fkRectColumnTranslationVertexEquiv R s x) (fkRectColumnTranslationVertexEquiv R s y) ↔ (fkRectOpenGraph R omega).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_columnTranslation_adj R s omega x y

/--
[fkRectOpenEdgeCount_columnTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectOpenEdgeCount_columnTranslation_eq
  {R : FKRectTorus}
  {s : Int}
  {omega : R.Configuration} :
-- imply
  fkRectOpenEdgeCount R (fkRectColumnTranslationConfigurationEquiv R s omega) = fkRectOpenEdgeCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectOpenEdgeCount_columnTranslation R s omega

/--
[fkRectNumClusters_columnTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectNumClusters_columnTranslation_eq
  {R : FKRectTorus}
  {s : Int}
  {omega : R.Configuration} :
-- imply
  fkRectNumClusters R (fkRectColumnTranslationConfigurationEquiv R s omega) = fkRectNumClusters R omega := by
-- proof
  apply StatMech.FrontierD.fkRectNumClusters_columnTranslation R s omega

/--
[fkRectCriticalReducedWeight_columnTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectCriticalReducedWeight_columnTranslation_eq
  {R : FKRectTorus}
  {s : Int}
  {q : Real}
  {omega : R.Configuration} :
-- imply
  fkRectCriticalReducedWeight R q (fkRectColumnTranslationConfigurationEquiv R s omega) = fkRectCriticalReducedWeight R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedWeight_columnTranslation R s q omega

/--
[fkRectCriticalReducedZ_columnTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectCriticalReducedZ_columnTranslation_eq
  {R : FKRectTorus}
  {s : Int}
  {q : Real} :
-- imply
  (∑ omega : R.Configuration, fkRectCriticalReducedWeight R q (fkRectColumnTranslationConfigurationEquiv R s omega)) = fkRectCriticalReducedZ R q := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedZ_columnTranslation R s q

/--
[fkRectCriticalRandomClusterProb_columnTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterProb_columnTranslation_eq
  {R : FKRectTorus}
  {s : Int}
  {q : Real}
  {omega : R.Configuration} :
-- imply
  fkRectCriticalRandomClusterProb R q (fkRectColumnTranslationConfigurationEquiv R s omega) = fkRectCriticalRandomClusterProb R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterProb_columnTranslation R s q omega

/--
[fkRectCriticalEventMass_columnTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectCriticalEventMass_columnTranslation_eq
  {R : FKRectTorus}
  {s : Int}
  {q : Real}
  {A : Set R.Configuration} :
-- imply
  fkRectCriticalEventMass R q A = fkRectCriticalEventMass R q ((fkRectColumnTranslationConfigurationEquiv R s) '' A) := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalEventMass_columnTranslation R s q A

/--
[fkRectConnectedWithin_columnTranslation_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectConnectedWithin_columnTranslation_iff_eq
  {R : FKRectTorus}
  {s : Int}
  {omega : R.Configuration}
  {S : Set R.Vertex}
  {x y : S} :
-- imply
  FKRectConnectedWithin R (fkRectColumnTranslationConfigurationEquiv R s omega) (fkRectColumnTranslationSet R s S) (fkRectColumnTranslationSetEquiv R s S x) (fkRectColumnTranslationSetEquiv R s S y) ↔ FKRectConnectedWithin R omega S x y := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedWithin_columnTranslation_iff R s omega S x y

/--
[fkRectCritical_connectedWithinMass_columnTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectCritical_connectedWithinMass_columnTranslation_eq
  {R : FKRectTorus}
  {s : Int}
  {q : Real}
  {S : Set R.Vertex}
  {x y : S} :
-- imply
  fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega (fkRectColumnTranslationSet R s S) (fkRectColumnTranslationSetEquiv R s S x) (fkRectColumnTranslationSetEquiv R s S y)} = fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega S x y} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_connectedWithinMass_columnTranslation R s q S x y

/--
[fkRectTorusIndexedEdge_columnSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectTorusIndexedEdge_columnSucc_eq
  {R : FKRectTorus}
  {a : R.EdgeIndex} :
-- imply
  fkRectTorusIndexedEdge R (fkRectColumnTranslationEdgeEquiv R 1 a) = Sym2.map (fkRectColumnTranslationVertexEquiv R 1) (fkRectTorusIndexedEdge R a) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusIndexedEdge_columnSucc R a

/--
[fkRectTorusGraph_adj_columnSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectTorusGraph_adj_columnSucc_eq
  {R : FKRectTorus}
  {x y : R.Vertex} :
-- imply
  (fkRectTorusGraph R).Adj (fkRectColumnTranslationVertexEquiv R 1 x) (fkRectColumnTranslationVertexEquiv R 1 y) ↔ (fkRectTorusGraph R).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectTorusGraph_adj_columnSucc R x y

/--
[fkRectOpenGraph_columnSucc_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectOpenGraph_columnSucc_adj_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {x y : R.Vertex} :
-- imply
  (fkRectOpenGraph R (fkRectColumnTranslationConfigurationEquiv R 1 omega)).Adj (fkRectColumnTranslationVertexEquiv R 1 x) (fkRectColumnTranslationVertexEquiv R 1 y) ↔ (fkRectOpenGraph R omega).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_columnSucc_adj R omega x y

/--
[fkRectCriticalRandomClusterProb_columnSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterProb_columnSucc_eq
  {R : FKRectTorus}
  {q : Real}
  {omega : R.Configuration} :
-- imply
  fkRectCriticalRandomClusterProb R q (fkRectColumnTranslationConfigurationEquiv R 1 omega) = fkRectCriticalRandomClusterProb R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterProb_columnSucc R q omega

/--
[fkRectConnectedWithin_columnSucc_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectConnectedWithin_columnSucc_iff_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {S : Set R.Vertex}
  {x y : S} :
-- imply
  FKRectConnectedWithin R (fkRectColumnTranslationConfigurationEquiv R 1 omega) (fkRectColumnTranslationSet R 1 S) (fkRectColumnTranslationSetEquiv R 1 S x) (fkRectColumnTranslationSetEquiv R 1 S y) ↔ FKRectConnectedWithin R omega S x y := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedWithin_columnSucc_iff R omega S x y

/--
[fkRectCritical_connectedWithinMass_columnSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectCritical_connectedWithinMass_columnSucc_eq
  {R : FKRectTorus}
  {q : Real}
  {S : Set R.Vertex}
  {x y : S} :
-- imply
  fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega (fkRectColumnTranslationSet R 1 S) (fkRectColumnTranslationSetEquiv R 1 S x) (fkRectColumnTranslationSetEquiv R 1 S y)} = fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega S x y} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_connectedWithinMass_columnSucc R q S x y

/--
[fkRectColumnTranslate_one_val_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectColumnTranslate_one_val_of_lt_eq
  {R : FKRectTorus}
  {x : Fin R.width}
-- given
  (hlt : x.val + 1 < R.width) :
-- imply
  (fkRectColumnTranslate R 1 x).val = x.val + 1 := by
-- proof
  apply StatMech.FrontierD.fkRectColumnTranslate_one_val_of_lt R x hlt

/--
[fkRectEvenRowTranslation_columnTranslation_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean)
-/
@[path]
private lemma fkRectEvenRowTranslation_columnTranslation_comm_eq
  {R : FKRectTorus}
  {step : Nat}
  {s : Int}
  {v : R.Vertex} :
-- imply
  fkRectEvenRowTranslationVertexEquiv R step (fkRectColumnTranslationVertexEquiv R s v) = fkRectColumnTranslationVertexEquiv R s (fkRectEvenRowTranslationVertexEquiv R step v) := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslation_columnTranslation_comm R step s v


-- created on 2026-10-23
