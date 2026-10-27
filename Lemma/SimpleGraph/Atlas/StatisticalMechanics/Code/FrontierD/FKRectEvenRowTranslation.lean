import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part7
open Set SimpleGraph StatMech.Lattice StatMech StatMech.FrontierD


/--
[fkRectRowTranslate_neg_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectRowTranslate_neg_left_eq
  {R : FKRectTorus}
  {s : Int}
  {y : Fin R.height} :
-- imply
  fkRectRowTranslate R (-s) (fkRectRowTranslate R s y) = y := by
-- proof
  apply StatMech.FrontierD.fkRectRowTranslate_neg_left R s y

/--
[fkRectRowTranslate_neg_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectRowTranslate_neg_right_eq
  {R : FKRectTorus}
  {s : Int}
  {y : Fin R.height} :
-- imply
  fkRectRowTranslate R s (fkRectRowTranslate R (-s) y) = y := by
-- proof
  apply StatMech.FrontierD.fkRectRowTranslate_neg_right R s y

/--
[fkRectRowTranslationEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectRowTranslationEquiv_apply_eq
  {R : FKRectTorus}
  {s : Int}
  {y : Fin R.height} :
-- imply
  fkRectRowTranslationEquiv R s y = fkRectRowTranslate R s y := by
-- proof
  apply StatMech.FrontierD.fkRectRowTranslationEquiv_apply R s y

/--
[fkRectRowTranslate_nat_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectRowTranslate_nat_val_eq
  {R : FKRectTorus}
  {s : Nat}
  {y : Fin R.height} :
-- imply
  (fkRectRowTranslate R s y).val = (y.val + s) % R.height := by
-- proof
  apply StatMech.FrontierD.fkRectRowTranslate_nat_val R s y

/--
[fkRectRowTranslate_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectRowTranslate_zero_eq
  {R : FKRectTorus}
  {y : Fin R.height} :
-- imply
  fkRectRowTranslate R 0 y = y := by
-- proof
  apply StatMech.FrontierD.fkRectRowTranslate_zero R y

/--
[fkRectRowTranslate_even_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectRowTranslate_even_iff_eq
  {R : FKRectTorus}
  {s : Nat}
  {y : Fin R.height}
-- given
  (hs : Even s) :
-- imply
  Even (fkRectRowTranslate R s y).val ↔ Even y.val := by
-- proof
  apply StatMech.FrontierD.fkRectRowTranslate_even_iff R s hs y

/--
[fkRectRowTranslate_cyclicPred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectRowTranslate_cyclicPred_eq
  {R : FKRectTorus}
  {s : Int}
  {y : Fin R.height} :
-- imply
  fkRectRowTranslate R s (SixVertexArrows.cyclicPred R.height_pos y) = SixVertexArrows.cyclicPred R.height_pos (fkRectRowTranslate R s y) := by
-- proof
  apply StatMech.FrontierD.fkRectRowTranslate_cyclicPred R s y

/--
[fkRectRowTranslate_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectRowTranslate_add_eq
  {R : FKRectTorus}
  {a b : Nat}
  {y : Fin R.height} :
-- imply
  fkRectRowTranslate R a (fkRectRowTranslate R b y) = fkRectRowTranslate R (a + b) y := by
-- proof
  apply StatMech.FrontierD.fkRectRowTranslate_add R a b y

/--
[fkRectEvenRowTranslationVertexEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectEvenRowTranslationVertexEquiv_apply_eq
  {R : FKRectTorus}
  {s : Nat}
  {v : R.Vertex} :
-- imply
  fkRectEvenRowTranslationVertexEquiv R s v = (v.1, fkRectRowTranslate R s v.2) := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslationVertexEquiv_apply R s v

/--
[fkRectEvenRowTranslationVertexEquiv_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectEvenRowTranslationVertexEquiv_add_eq
  {R : FKRectTorus}
  {a b : Nat}
  {v : R.Vertex} :
-- imply
  fkRectEvenRowTranslationVertexEquiv R a (fkRectEvenRowTranslationVertexEquiv R b v) = fkRectEvenRowTranslationVertexEquiv R (a + b) v := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslationVertexEquiv_add R a b v

/--
[fkRectEvenRowTranslationVertexEquiv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectEvenRowTranslationVertexEquiv_zero_eq
  {R : FKRectTorus}
  {v : R.Vertex} :
-- imply
  fkRectEvenRowTranslationVertexEquiv R 0 v = v := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslationVertexEquiv_zero R v

/--
[fkRectEvenRowTranslationEdgeEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectEvenRowTranslationEdgeEquiv_apply_eq
  {R : FKRectTorus}
  {s : Nat}
  {a : R.EdgeIndex} :
-- imply
  fkRectEvenRowTranslationEdgeEquiv R s a = (a.1, (a.2.1, fkRectRowTranslate R s a.2.2)) := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslationEdgeEquiv_apply R s a

/--
[fkRectTorusIndexedEdge_evenRowTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectTorusIndexedEdge_evenRowTranslation_eq
  {R : FKRectTorus}
  {s : Nat}
  {a : R.EdgeIndex}
-- given
  (hs : Even s) :
-- imply
  fkRectTorusIndexedEdge R (fkRectEvenRowTranslationEdgeEquiv R s a) = Sym2.map (fkRectEvenRowTranslationVertexEquiv R s) (fkRectTorusIndexedEdge R a) := by
-- proof
  apply StatMech.FrontierD.fkRectTorusIndexedEdge_evenRowTranslation R s hs a

/--
[fkRectTorusGraph_adj_evenRowTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectTorusGraph_adj_evenRowTranslation_eq
  {R : FKRectTorus}
  {s : Nat}
  {x y : R.Vertex}
-- given
  (hs : Even s) :
-- imply
  (fkRectTorusGraph R).Adj (fkRectEvenRowTranslationVertexEquiv R s x) (fkRectEvenRowTranslationVertexEquiv R s y) ↔ (fkRectTorusGraph R).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectTorusGraph_adj_evenRowTranslation R s hs x y

/--
[fkRectEvenRowTranslationConfigurationEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectEvenRowTranslationConfigurationEquiv_apply_eq
  {R : FKRectTorus}
  {s : Nat}
  {omega : R.Configuration}
  {a : R.EdgeIndex} :
-- imply
  fkRectEvenRowTranslationConfigurationEquiv R s omega a = omega ((fkRectEvenRowTranslationEdgeEquiv R s).symm a) := by
-- proof
  apply StatMech.FrontierD.fkRectEvenRowTranslationConfigurationEquiv_apply R s omega a

/--
[fkRectOpenGraph_evenRowTranslation_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectOpenGraph_evenRowTranslation_adj_eq
  {R : FKRectTorus}
  {s : Nat}
  {omega : R.Configuration}
  {x y : R.Vertex}
-- given
  (hs : Even s) :
-- imply
  (fkRectOpenGraph R (fkRectEvenRowTranslationConfigurationEquiv R s omega)).Adj (fkRectEvenRowTranslationVertexEquiv R s x) (fkRectEvenRowTranslationVertexEquiv R s y) ↔ (fkRectOpenGraph R omega).Adj x y := by
-- proof
  apply StatMech.FrontierD.fkRectOpenGraph_evenRowTranslation_adj R s hs omega x y

/--
[fkRectOpenEdgeCount_evenRowTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectOpenEdgeCount_evenRowTranslation_eq
  {R : FKRectTorus}
  {s : Nat}
  {omega : R.Configuration} :
-- imply
  fkRectOpenEdgeCount R (fkRectEvenRowTranslationConfigurationEquiv R s omega) = fkRectOpenEdgeCount R omega := by
-- proof
  apply StatMech.FrontierD.fkRectOpenEdgeCount_evenRowTranslation R s omega

/--
[fkRectNumClusters_evenRowTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectNumClusters_evenRowTranslation_eq
  {R : FKRectTorus}
  {s : Nat}
  {omega : R.Configuration}
-- given
  (hs : Even s) :
-- imply
  fkRectNumClusters R (fkRectEvenRowTranslationConfigurationEquiv R s omega) = fkRectNumClusters R omega := by
-- proof
  apply StatMech.FrontierD.fkRectNumClusters_evenRowTranslation R s hs omega

/--
[fkRectCriticalReducedWeight_evenRowTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectCriticalReducedWeight_evenRowTranslation_eq
  {R : FKRectTorus}
  {s : Nat}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hs : Even s) :
-- imply
  fkRectCriticalReducedWeight R q (fkRectEvenRowTranslationConfigurationEquiv R s omega) = fkRectCriticalReducedWeight R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalReducedWeight_evenRowTranslation R s hs q omega

/--
[fkRectCriticalRandomClusterProb_evenRowTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectCriticalRandomClusterProb_evenRowTranslation_eq
  {R : FKRectTorus}
  {s : Nat}
  {q : Real}
  {omega : R.Configuration}
-- given
  (hs : Even s) :
-- imply
  fkRectCriticalRandomClusterProb R q (fkRectEvenRowTranslationConfigurationEquiv R s omega) = fkRectCriticalRandomClusterProb R q omega := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalRandomClusterProb_evenRowTranslation R s hs q omega

/--
[fkRectConnectedWithin_evenRowTranslation_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectConnectedWithin_evenRowTranslation_iff_eq
  {R : FKRectTorus}
  {s : Nat}
  {omega : R.Configuration}
  {S : Set R.Vertex}
  {x y : S}
-- given
  (hs : Even s) :
-- imply
  FKRectConnectedWithin R (fkRectEvenRowTranslationConfigurationEquiv R s omega) (fkRectEvenRowTranslationSet R s S) (fkRectEvenRowTranslationSetEquiv R s S x) (fkRectEvenRowTranslationSetEquiv R s S y) ↔ FKRectConnectedWithin R omega S x y := by
-- proof
  apply StatMech.FrontierD.fkRectConnectedWithin_evenRowTranslation_iff R s hs omega S x y

/--
[fkRectCritical_connectedWithinMass_evenRowTranslation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean)
-/
@[path]
private lemma fkRectCritical_connectedWithinMass_evenRowTranslation_eq
  {R : FKRectTorus}
  {s : Nat}
  {q : Real}
  {S : Set R.Vertex}
  {x y : S}
-- given
  (hs : Even s) :
-- imply
  fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega (fkRectEvenRowTranslationSet R s S) (fkRectEvenRowTranslationSetEquiv R s S x) (fkRectEvenRowTranslationSetEquiv R s S y)} = fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega S x y} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_connectedWithinMass_evenRowTranslation R s hs q S x y


-- created on 2026-10-23
