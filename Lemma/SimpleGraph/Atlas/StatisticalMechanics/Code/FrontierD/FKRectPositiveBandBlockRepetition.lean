import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectPositiveBandBlockRepetition
open Set SimpleGraph Filter Topology StatMech StatMech.FrontierD


/--
[FKRectPositiveBandOrientedBlock.step_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma step_pos_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hscale : 3 ≤ scale) :
-- imply
  0 < B.step := by
-- proof
  apply StatMech.FrontierD.FKRectPositiveBandOrientedBlock.step_pos B hscale

/--
[fkRectPositiveBandBulkBlocks_mul_step_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBulkBlocks_mul_step_le_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale} :
-- imply
  fkRectPositiveBandBulkBlocks B * B.step ≤ R.height - 1 - (24 * scale + 4) := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBulkBlocks_mul_step_le B

/--
[fkRectPositiveBandBulkBlocks_remainder_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBulkBlocks_remainder_lt_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hscale : 3 ≤ scale) :
-- imply
  R.height - 1 - (24 * scale + 4) - fkRectPositiveBandBulkBlocks B * B.step < B.step := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBulkBlocks_remainder_lt B hscale

/--
[fkRectPositiveBandBlockPathVertex_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBlockPathVertex_val_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
  {i : Fin (fkRectPositiveBandBulkBlocks B + 1)}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1) :
-- imply
  (fkRectPositiveBandBlockPathVertex B hheight i).1 = fkRectEvenRowTranslationVertexEquiv R (i.val * B.step) B.start.1 := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBlockPathVertex_val B hheight i

/--
[fkRectPositiveBandBlockPathVertex_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBlockPathVertex_pair_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
  {i : Fin (fkRectPositiveBandBulkBlocks B)}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1) :
-- imply
  ((fkRectPositiveBandBlockPathVertex B hheight i.castSucc).1, (fkRectPositiveBandBlockPathVertex B hheight i.succ).1) = (fkRectEvenRowTranslationVertexEquiv R (i.val * B.step) B.start.1, fkRectEvenRowTranslationVertexEquiv R (i.val * B.step) B.finish.1) := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBlockPathVertex_pair B hheight i

/--
[fkRectPositiveBandBlockAuxiliaryPairs_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBlockAuxiliaryPairs_spans_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1) :
-- imply
  FKRectColumnBandConnectionChainSpans R 1 (4 * scale + 1) (fkRectUnitGapColumn R) (by rfl) (by simp [fkRectUnitGapColumn]) (fkRectPositiveBandBlockAuxiliaryPairs B hheight) := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBlockAuxiliaryPairs_spans B hheight

/--
[fkRectInduced_openSub_fullGraphConfiguration_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectInduced_openSub_fullGraphConfiguration_eq_eq
  {R : FKRectTorus}
  {omega : R.Configuration}
  {S : Set R.Vertex} :
-- imply
  FK.openSub (fkRectInducedGraph R S) (FK.ocd_innerRestrict (Subtype.val : FKRectInducedVertex R S → R.Vertex) (fkRectFullGraphConfiguration R omega)) = (fkRectOpenGraph R omega).induce S := by
-- proof
  apply StatMech.FrontierD.fkRectInduced_openSub_fullGraphConfiguration_eq R omega S

/--
[fkRectCritical_inducedTwoPoint_le_connectedWithinMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectCritical_inducedTwoPoint_le_connectedWithinMass_eq
  {R : FKRectTorus}
  {S : Set R.Vertex}
  {q : Real}
  {x y : FKRectInducedVertex R S}
-- given
  (hq : 1 ≤ q) :
-- imply
  FK.twoPointFun (fkRectInducedGraph R S) (fkRectCriticalP q) q x y ≤ fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega S x y} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_inducedTwoPoint_le_connectedWithinMass R S hq x y

/--
[fkRectColumnBand_reachable_horizontalPred_of_lower_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectColumnBand_reachable_horizontalPred_of_lower_lt_eq
  {R : FKRectTorus}
  {right lower upper : Nat}
  {x : Fin R.width}
  {y : Fin R.height}
-- given
  (hxleft : 1 < x.val)
  (hxright : x.val ≤ right)
  (hylower : lower < y.val)
  (hyupper : y.val ≤ upper) :
-- imply
  let xp := SixVertexArrows.cyclicPred R.width_pos x (fkRectInducedGraph R (fkRectColumnBand R 1 right lower upper)).Reachable ⟨(x, y), by change 1 ≤ x.val ∧ x.val ≤ right ∧ lower ≤ y.val ∧ y.val ≤ upper omega⟩ ⟨(xp, y), by change 1 ≤ xp.val ∧ xp.val ≤ right ∧ lower ≤ y.val ∧ y.val ≤ upper rw [fkRectCyclicPred_val] split <;> omega⟩ := by
-- proof
  apply StatMech.FrontierD.fkRectColumnBand_reachable_horizontalPred_of_lower_lt R right lower upper x y hxleft hxright hylower hyupper

/--
[fkRectColumnBand_reachable_horizontalPred](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectColumnBand_reachable_horizontalPred_eq
  {R : FKRectTorus}
  {right lower upper : Nat}
  {x : Fin R.width}
  {y : Fin R.height}
-- given
  (hlowerUpper : lower < upper)
  (hupper : upper < R.height)
  (hxleft : 1 < x.val)
  (hxright : x.val ≤ right)
  (hylower : lower ≤ y.val)
  (hyupper : y.val ≤ upper) :
-- imply
  let xp := SixVertexArrows.cyclicPred R.width_pos x (fkRectInducedGraph R (fkRectColumnBand R 1 right lower upper)).Reachable ⟨(x, y), by change 1 ≤ x.val ∧ x.val ≤ right ∧ lower ≤ y.val ∧ y.val ≤ upper omega⟩ ⟨(xp, y), by change 1 ≤ xp.val ∧ xp.val ≤ right ∧ lower ≤ y.val ∧ y.val ≤ upper rw [fkRectCyclicPred_val] split <;> omega⟩ := by
-- proof
  apply StatMech.FrontierD.fkRectColumnBand_reachable_horizontalPred R right lower upper hlowerUpper hupper x y hxleft hxright hylower hyupper

/--
[fkRectColumnBandGrid_adj_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectColumnBandGrid_adj_reachable_eq
  {R : FKRectTorus}
  {right lower upper : Nat}
  {z w : Fin right × Fin (upper + 1 - lower)}
-- given
  (hrightPos : 1 ≤ right)
  (hright : right < R.width)
  (hlowerUpper : lower < upper)
  (hupper : upper < R.height)
  (hzw : ((pathGraph right) □ (pathGraph (upper + 1 - lower))).Adj z w) :
-- imply
  (fkRectInducedGraph R (fkRectColumnBand R 1 right lower upper)).Reachable (fkRectColumnBandGridEquiv R right lower upper hright hlowerUpper.le hupper z) (fkRectColumnBandGridEquiv R right lower upper hright hlowerUpper.le hupper w) := by
-- proof
  apply StatMech.FrontierD.fkRectColumnBandGrid_adj_reachable R right lower upper hrightPos hright hlowerUpper hupper hzw

/--
[fkRectColumnBand_preconnected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectColumnBand_preconnected_eq
  {R : FKRectTorus}
  {right lower upper : Nat}
-- given
  (hrightPos : 1 ≤ right)
  (hright : right < R.width)
  (hlowerUpper : lower < upper)
  (hupper : upper < R.height) :
-- imply
  (fkRectInducedGraph R (fkRectColumnBand R 1 right lower upper)).Preconnected := by
-- proof
  apply StatMech.FrontierD.fkRectColumnBand_preconnected R right lower upper hrightPos hright hlowerUpper hupper

/--
[fkRectColumnBand_fintype_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectColumnBand_fintype_card_eq
  {R : FKRectTorus}
  {right lower upper : Nat}
-- given
  (hright : right < R.width)
  (hlowerUpper : lower ≤ upper)
  (hupper : upper < R.height) :
-- imply
  Fintype.card (FKRectColumnBandVertex R 1 right lower upper) = right * (upper + 1 - lower) := by
-- proof
  apply StatMech.FrontierD.fkRectColumnBand_fintype_card R right lower upper hright hlowerUpper hupper

/--
[fkRectCritical_cFE_pow_bandCard_le_connectedWithinMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_bandCard_le_connectedWithinMass_eq
  {R : FKRectTorus}
  {right lower upper : Nat}
  {q : Real}
  {x y : FKRectColumnBandVertex R 1 right lower upper}
-- given
  (hrightPos : 1 ≤ right)
  (hright : right < R.width)
  (hlowerUpper : lower < upper)
  (hupper : upper < R.height)
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (right * (upper + 1 - lower)) ≤ fkRectCriticalEventMass R q {omega | FKRectConnectedWithin R omega (fkRectColumnBand R 1 right lower upper) x y} := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_bandCard_le_connectedWithinMass R right lower upper hrightPos hright hlowerUpper hupper hq x y

/--
[fkRectPositiveBandBlock_translatedCarrier_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBlock_translatedCarrier_subset_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
  {i : Nat}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1)
  (hi : i < fkRectPositiveBandBulkBlocks B) :
-- imply
  fkRectEvenRowTranslationSet R (i * B.step) B.carrier ⊆ fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1) := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBlock_translatedCarrier_subset B hheight i hi

/--
[fkRectPositiveBandBlockIntersection_inducedChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBlockIntersection_inducedChain_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
  {omega : R.Configuration}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1)
  (hmem : omega ∈ fkRectEvenRowBlockIntersection R B.carrier B.start B.finish B.step (fkRectPositiveBandBulkBlocks B)) :
-- imply
  FK.ocd_innerRestrict (Subtype.val : FKRectColumnBandVertex R 1 (4 * scale + 1) 1 (R.height - 1) → R.Vertex) (fkRectFullGraphConfiguration R omega) ∈ fkRectInducedConnectionChainEvent R (fkRectColumnBand R 1 (4 * scale + 1) 1 (R.height - 1)) (fkRectPositiveBandBlockBulkPairs B hheight) := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBlockIntersection_inducedChain B hheight omega hmem

/--
[fkRectPositiveBandBlockBottomConnectorEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBlockBottomConnectorEvent_isIncreasing_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1) :
-- imply
  IsIncreasing (fkRectPositiveBandBlockBottomConnectorEvent B hheight) := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBlockBottomConnectorEvent_isIncreasing B hheight

/--
[fkRectPositiveBandBlockTopConnectorEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBlockTopConnectorEvent_isIncreasing_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1) :
-- imply
  IsIncreasing (fkRectPositiveBandBlockTopConnectorEvent B hheight) := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBlockTopConnectorEvent_isIncreasing B hheight

/--
[fkRectCritical_cFE_pow_le_bottomConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_le_bottomConnector_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1)
  (hproper : 4 * scale + 1 < R.width)
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ ((4 * scale + 1) * (24 * scale + 4)) ≤ fkRectCriticalEventMass R q (fkRectPositiveBandBlockBottomConnectorEvent B hheight) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_le_bottomConnector B hheight hproper hq

/--
[fkRectPositiveBandBlockPathVertex_last_row_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBlockPathVertex_last_row_lower_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1)
  (hscale : 3 ≤ scale) :
-- imply
  R.height - 1 - (40 * scale + 6) ≤ (fkRectPositiveBandBlockPathVertex B hheight (Fin.last (fkRectPositiveBandBulkBlocks B))).1.2.val := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBlockPathVertex_last_row_lower B hheight hscale

/--
[fkRectCritical_cFE_pow_le_topConnector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectCritical_cFE_pow_le_topConnector_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1)
  (hscale : 3 ≤ scale)
  (htall : 40 * scale + 6 < R.height - 1)
  (hproper : 4 * scale + 1 < R.width)
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ ((4 * scale + 1) * (40 * scale + 7)) ≤ fkRectCriticalEventMass R q (fkRectPositiveBandBlockTopConnectorEvent B hheight) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_pow_le_topConnector B hheight hscale htall hproper hq

/--
[fkRectUnitAttachmentOpenEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectUnitAttachmentOpenEvent_isIncreasing_eq
  {R : FKRectTorus} :
-- imply
  IsIncreasing (fkRectUnitAttachmentOpenEvent R) := by
-- proof
  apply StatMech.FrontierD.fkRectUnitAttachmentOpenEvent_isIncreasing R

/--
[fkRectCriticalOpenMass_singleton_eq_eventMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectCriticalOpenMass_singleton_eq_eventMass_eq
  {R : FKRectTorus}
  {q : Real}
  {a : R.EdgeIndex} :
-- imply
  fkRectCriticalOpenMass R q {a} = fkRectCriticalEventMass R q {omega | omega a = true} := by
-- proof
  apply StatMech.FrontierD.fkRectCriticalOpenMass_singleton_eq_eventMass R q a

/--
[fkRectCritical_cFE_le_unitAttachmentOpenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectCritical_cFE_le_unitAttachmentOpenEvent_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ≤ fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_cFE_le_unitAttachmentOpenEvent R hq

/--
[fkRectPositiveBandBlockAssembledEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBlockAssembledEvent_isIncreasing_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1) :
-- imply
  IsIncreasing (fkRectPositiveBandBlockAssembledEvent B hheight) := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBlockAssembledEvent_isIncreasing B hheight

/--
[fkRectPositiveBandBlock_auxiliary_of_bulk_connectors](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBlock_auxiliary_of_bulk_connectors_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
  {omega : R.Configuration}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1)
  (hbulk : omega ∈ fkRectEvenRowBlockIntersection R B.carrier B.start B.finish B.step (fkRectPositiveBandBulkBlocks B))
  (hbottom : omega ∈ fkRectPositiveBandBlockBottomConnectorEvent B hheight)
  (htop : omega ∈ fkRectPositiveBandBlockTopConnectorEvent B hheight)
  (hattach : omega ∈ fkRectUnitAttachmentOpenEvent R) :
-- imply
  omega ∈ fkRectUnitDualBarrierAuxiliary R (4 * scale + 1) (fkRectPositiveBandBlockAuxiliaryPairs B hheight) := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBlock_auxiliary_of_bulk_connectors B hheight omega hbulk hbottom htop hattach

/--
[fkRectPositiveBandBlockAssembledEvent_subset_auxiliary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectPositiveBandBlockAssembledEvent_subset_auxiliary_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1) :
-- imply
  fkRectPositiveBandBlockAssembledEvent B hheight ⊆ fkRectUnitDualBarrierAuxiliary R (4 * scale + 1) (fkRectPositiveBandBlockAuxiliaryPairs B hheight) := by
-- proof
  apply StatMech.FrontierD.fkRectPositiveBandBlockAssembledEvent_subset_auxiliary B hheight

/--
[exists_fkRectPositiveBandBlock_localizedVerticalCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma exists_fkRectPositiveBandBlock_localizedVerticalCycle_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
  {omega : R.Configuration}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1)
  (hproper : 4 * scale + 2 < R.width)
  (hbulk : omega ∈ fkRectEvenRowBlockIntersection R B.carrier B.start B.finish B.step (fkRectPositiveBandBulkBlocks B))
  (hbottom : omega ∈ fkRectPositiveBandBlockBottomConnectorEvent B hheight)
  (htop : omega ∈ fkRectPositiveBandBlockTopConnectorEvent B hheight)
  (hattach : omega ∈ fkRectUnitAttachmentOpenEvent R) :
-- imply
  let forced := fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))) omega ∃ z : (fkRectOpenGraph R forced).Walk (fkRectRowOneVertex R (fkRectUnitGapColumn R)) (fkRectRowOneVertex R (fkRectUnitGapColumn R)), fkRectWalkWinding R z = (0, 1) ∧ ∀ v ∈ z.support, 1 ≤ v.1.val ∧ v.1.val ≤ 4 * scale + 1 := by
-- proof
  apply StatMech.FrontierD.exists_fkRectPositiveBandBlock_localizedVerticalCycle B hheight hproper omega hbulk hbottom htop hattach

/--
[fkRectCritical_positiveBandBulkLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectCritical_positiveBandBulkLower_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hq : 1 ≤ q) :
-- imply
  B.massFloor ^ fkRectPositiveBandBulkBlocks B ≤ fkRectCriticalEventMass R q (fkRectEvenRowBlockIntersection R B.carrier B.start B.finish B.step (fkRectPositiveBandBulkBlocks B)) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_positiveBandBulkLower B hq

/--
[fkRectCritical_positiveBandAuxiliaryLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectCritical_positiveBandAuxiliaryLower_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
  {bottom top attachment : Real}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1)
  (hq : 1 ≤ q)
  (hbottom0 : 0 ≤ bottom)
  (htop0 : 0 ≤ top)
  (hattachment0 : 0 ≤ attachment)
  (hbottom : bottom ≤ fkRectCriticalEventMass R q (fkRectPositiveBandBlockBottomConnectorEvent B hheight))
  (htop : top ≤ fkRectCriticalEventMass R q (fkRectPositiveBandBlockTopConnectorEvent B hheight))
  (hattachment : attachment ≤ fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R)) :
-- imply
  ((B.massFloor ^ fkRectPositiveBandBulkBlocks B * bottom) * top) * attachment ≤ fkRectCriticalEventMass R q (fkRectUnitDualBarrierAuxiliary R (4 * scale + 1) (fkRectPositiveBandBlockAuxiliaryPairs B hheight)) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_positiveBandAuxiliaryLower B hheight hq hbottom0 htop0 hattachment0 hbottom htop hattachment

/--
[fkRectCritical_concretePositiveBandAuxiliaryLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectCritical_concretePositiveBandAuxiliaryLower_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1)
  (hscale : 3 ≤ scale)
  (htall : 40 * scale + 6 < R.height - 1)
  (hproper : 4 * scale + 1 < R.width)
  (hq : 1 ≤ q) :
-- imply
  ((B.massFloor ^ fkRectPositiveBandBulkBlocks B * FK.cFE (fkRectCriticalP q) q ^ ((4 * scale + 1) * (24 * scale + 4))) * FK.cFE (fkRectCriticalP q) q ^ ((4 * scale + 1) * (40 * scale + 7))) * FK.cFE (fkRectCriticalP q) q ≤ fkRectCriticalEventMass R q (fkRectUnitDualBarrierAuxiliary R (4 * scale + 1) (fkRectPositiveBandBlockAuxiliaryPairs B hheight)) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_concretePositiveBandAuxiliaryLower B hheight hscale htall hproper hq

/--
[fkRectCritical_concretePositiveBandDualBarrierLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectCritical_concretePositiveBandDualBarrierLower_eq
  {R : FKRectTorus}
  {q : Real}
  {scale : Nat}
  {B : FKRectPositiveBandOrientedBlock R q scale}
-- given
  (hheight : 24 * scale + 4 ≤ R.height - 1)
  (hscale : 3 ≤ scale)
  (htall : 40 * scale + 6 < R.height - 1)
  (hproper : 4 * scale + 2 < R.width)
  (hq : 1 ≤ q) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * R.width) * (((B.massFloor ^ fkRectPositiveBandBulkBlocks B * FK.cFE (fkRectCriticalP q) q ^ ((4 * scale + 1) * (24 * scale + 4))) * FK.cFE (fkRectCriticalP q) q ^ ((4 * scale + 1) * (40 * scale + 7))) * FK.cFE (fkRectCriticalP q) q) ≤ fkRectCriticalEventMass R q (fkRectDualPullbackSourceLeftBarrier R (4 * scale + 1) (fkRectUnitLeftBarrierGap R)) := by
-- proof
  apply StatMech.FrontierD.fkRectCritical_concretePositiveBandDualBarrierLower B hheight hscale htall hproper hq

/--
[fkRectWindingBlock_sourceBarrier_eventualUpper_of_eventuallyDualPullback_mul_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPositiveBandBlockRepetition.lean)
-/
@[path]
private lemma fkRectWindingBlock_sourceBarrier_eventualUpper_of_eventuallyDualPullback_mul_pow_eq
  {k scale leftRight : Nat}
  {q C a : Real}
-- given
  (hone : 1 ≤ leftRight)
  (hleft : leftRight + 1 < 2 * (k + 3))
  (hq : 1 ≤ q)
  (hC : 0 < C)
  (ha : 0 < a)
  (haux : ∀ᶠ blocks in atTop, C * a ^ (blocks + 1) ≤ fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDualPullbackSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) :
-- imply
  ∀ epsilon : Real, 0 < epsilon → ∀ᶠ blocks in atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height ≤ -Real.log a / (2 * (scale + 1) : Real) + epsilon := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_sourceBarrier_eventualUpper_of_eventuallyDualPullback_mul_pow k scale leftRight hone hleft hq hC ha haux


-- created on 2026-10-23
