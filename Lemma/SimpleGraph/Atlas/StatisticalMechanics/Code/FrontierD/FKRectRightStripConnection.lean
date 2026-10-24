import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection
open StatMech StatMech.FrontierD


/--
[fkRect_innerEdge_subtype_mk_mem_range_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean)
-/
@[path]
private lemma fkRect_innerEdge_subtype_mk_mem_range_iff_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {x y : R.Vertex} :
-- imply
  s(x, y) ∈ Set.range (FK.ocd_innerEdge (Subtype.val : FKRectInducedVertex R S → R.Vertex)) ↔ x ∈ S ∧ y ∈ S := by
-- proof
  apply StatMech.FrontierD.fkRect_innerEdge_subtype_mk_mem_range_iff R S x y

/--
[fkRect_verticalSeam_not_innerEdgeRange_of_rowZero_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean)
-/
@[path]
private lemma fkRect_verticalSeam_not_innerEdgeRange_of_rowZero_disjoint_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {e : Sym2 R.Vertex}
-- given
  (hzero : ∀ v ∈ S, v.2.val ≠ 0)
  (he : fkRectCrossesVerticalSeam R e) :
-- imply
  e ∉ Set.range (FK.ocd_innerEdge (Subtype.val : FKRectInducedVertex R S → R.Vertex)) := by
-- proof
  apply StatMech.FrontierD.fkRect_verticalSeam_not_innerEdgeRange_of_rowZero_disjoint R S hzero he

/--
[fkRect_verticalSeam_not_rightStripBand_innerEdgeRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean)
-/
@[path]
private lemma fkRect_verticalSeam_not_rightStripBand_innerEdgeRange_eq
  {R : FKRectTorus}
  {cut lower upper : Nat}
  {e : Sym2 R.Vertex}
-- given
  (hlower : 1 ≤ lower)
  (he : fkRectCrossesVerticalSeam R e) :
-- imply
  e ∉ Set.range (FK.ocd_innerEdge (Subtype.val : FKRectRightStripBandVertex R cut lower upper → R.Vertex)) := by
-- proof
  apply StatMech.FrontierD.fkRect_verticalSeam_not_rightStripBand_innerEdgeRange R cut lower upper hlower he

/--
[fkRectIndexedPatternEvent_dependsOnOutsideRegion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean)
-/
@[path]
private lemma fkRectIndexedPatternEvent_dependsOnOutsideRegion_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {I : Finset R.EdgeIndex}
  {eta : R.Configuration}
-- given
  (hI : ∀ a ∈ I, fkRectTorusIndexedEdge R a ∉ Set.range (FK.ocd_innerEdge (Subtype.val : FKRectInducedVertex R S → R.Vertex))) :
-- imply
  FKRectDependsOnOutsideRegion R S (fkRectIndexedPatternEvent R I eta) := by
-- proof
  apply StatMech.FrontierD.fkRectIndexedPatternEvent_dependsOnOutsideRegion R S I eta hI

/--
[fkRectVerticalSeamPattern_dependsOnOutsideRightStripBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean)
-/
@[path]
private lemma fkRectVerticalSeamPattern_dependsOnOutsideRightStripBand_eq
  {R : FKRectTorus}
  {cut lower upper : Nat}
  {I : Finset R.EdgeIndex}
  {eta : R.Configuration}
-- given
  (hlower : 1 ≤ lower)
  (hI : ∀ a ∈ I, fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R a)) :
-- imply
  FKRectDependsOnOutsideRegion R (fkRectRightStripBand R cut lower upper) (fkRectIndexedPatternEvent R I eta) := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamPattern_dependsOnOutsideRightStripBand R cut lower upper hlower I hI eta

/--
[fkRectInducedConnectionChainEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean)
-/
@[path]
private lemma fkRectInducedConnectionChainEvent_isIncreasing_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S)} :
-- imply
  IsIncreasing (fkRectInducedConnectionChainEvent R S t) := by
-- proof
  apply StatMech.FrontierD.fkRectInducedConnectionChainEvent_isIncreasing R S t

/--
[fkRectInduced_connectionChain_ge_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean)
-/
@[path]
private lemma fkRectInduced_connectionChain_ge_prod_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {p q : Real}
  {t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R S) p q xy.1 xy.2) ≤ ∑ omega, FK.fkProb (fkRectInducedGraph R S) p q omega * (fkRectInducedConnectionChainEvent R S t).indicator (fun _ => (1 : Real)) omega := by
-- proof
  apply StatMech.FrontierD.fkRectInduced_connectionChain_ge_prod R S hp hp1 hq t

/--
[fkRectInduced_connectionProduct_mul_outsideMass_le_genericInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean)
-/
@[path]
private lemma fkRectInduced_connectionProduct_mul_outsideMass_le_genericInter_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {q : Real}
  {t : Finset (FKRectInducedVertex R S × FKRectInducedVertex R S)}
  {B : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hB : FKRectDependsOnOutsideRegion R S B) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R S) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q B ≤ ∑ rho, ((FK.ocd_innerRestrict (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹' fkRectInducedConnectionChainEvent R S t) ∩ fkRectFullGraphEvent R B).indicator (fun _ => (1 : Real)) rho * FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q rho := by
-- proof
  apply StatMech.FrontierD.fkRectInduced_connectionProduct_mul_outsideMass_le_genericInter R S hq t hB

/--
[fkRectRightStrip_connectionProduct_mul_outsideMass_le_genericInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean)
-/
@[path]
private lemma fkRectRightStrip_connectionProduct_mul_outsideMass_le_genericInter_eq
  {R : FKRectTorus}
  {cut : Nat}
  {q : Real}
  {t : Finset (FKRectRightStripVertex R cut × FKRectRightStripVertex R cut)}
  {B : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hB : FKRectDependsOnOutsideRegion R (fkRectRightStrip R cut) B) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStrip R cut)) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q B ≤ ∑ rho, ((FK.ocd_innerRestrict (Subtype.val : FKRectRightStripVertex R cut → R.Vertex) ⁻¹' fkRectInducedConnectionChainEvent R (fkRectRightStrip R cut) t) ∩ fkRectFullGraphEvent R B).indicator (fun _ => (1 : Real)) rho * FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q rho := by
-- proof
  apply StatMech.FrontierD.fkRectRightStrip_connectionProduct_mul_outsideMass_le_genericInter R cut hq t hB

/--
[fkRectRightStripBand_connectionProduct_mul_outsideMass_le_genericInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightStripConnection.lean)
-/
@[path]
private lemma fkRectRightStripBand_connectionProduct_mul_outsideMass_le_genericInter_eq
  {R : FKRectTorus}
  {cut lower upper : Nat}
  {q : Real}
  {t : Finset (FKRectRightStripBandVertex R cut lower upper × FKRectRightStripBandVertex R cut lower upper)}
  {B : Set R.Configuration}
-- given
  (hq : 1 ≤ q)
  (hB : FKRectDependsOnOutsideRegion R (fkRectRightStripBand R cut lower upper) B) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper)) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q B ≤ ∑ rho, ((FK.ocd_innerRestrict (Subtype.val : FKRectRightStripBandVertex R cut lower upper → R.Vertex) ⁻¹' fkRectInducedConnectionChainEvent R (fkRectRightStripBand R cut lower upper) t) ∩ fkRectFullGraphEvent R B).indicator (fun _ => (1 : Real)) rho * FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q rho := by
-- proof
  apply StatMech.FrontierD.fkRectRightStripBand_connectionProduct_mul_outsideMass_le_genericInter R cut lower upper hq t hB


-- created on 2026-10-23
