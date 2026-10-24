import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierAuxiliary
open StatMech StatMech.FrontierD


/--
[fkRectColumnBand_connection_reachable_verticalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean)
-/
@[path]
private lemma fkRectColumnBand_connection_reachable_verticalCut_eq
  {R : FKRectTorus}
  {left right lower upper : Nat}
  {omega : R.Configuration}
  {x y : FKRectColumnBandVertex R left right lower upper}
-- given
  (hlower : 1 <= lower)
  (hxy : FK.ocd_innerRestrict (Subtype.val : FKRectColumnBandVertex R left right lower upper -> R.Vertex) (fkRectFullGraphConfiguration R omega) ∈ FK.connEvent (fkRectInducedGraph R (fkRectColumnBand R left right lower upper)) x y) :
-- imply
  (fkRectVerticalCutGraph R omega).Reachable x.1 y.1 := by
-- proof
  apply StatMech.FrontierD.fkRectColumnBand_connection_reachable_verticalCut R left right lower upper hlower omega x y hxy

/--
[fkRectColumnBandConnectionChainSpans_connectionPathPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean)
-/
@[path]
private lemma fkRectColumnBandConnectionChainSpans_connectionPathPairs_eq
  {R : FKRectTorus}
  {left right : Nat}
  {x : Fin R.width}
  {n : Nat}
-- given
  (hleft : left <= x.val)
  (hright : x.val <= right)
  (v : Fin (n + 1) -> FKRectColumnBandVertex R left right 1 (R.height - 1))
  (hfirst : v 0 = fkRectColumnBandRowOne R left right x hleft hright)
  (hlast : v (Fin.last n) = fkRectColumnBandLastRow R left right x hleft hright) :
-- imply
  FKRectColumnBandConnectionChainSpans R left right x hleft hright (connectionPathPairs n v) := by
-- proof
  apply StatMech.FrontierD.fkRectColumnBandConnectionChainSpans_connectionPathPairs R left right x hleft hright n v hfirst hlast

/--
[fkRectUnitAttachmentOpenEvent_dependsOnOutsideColumnBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean)
-/
@[path]
private lemma fkRectUnitAttachmentOpenEvent_dependsOnOutsideColumnBand_eq
  {R : FKRectTorus}
  {left right lower upper : Nat}
-- given
  (hlower : 1 <= lower) :
-- imply
  FKRectDependsOnOutsideRegion R (fkRectColumnBand R left right lower upper) (fkRectUnitAttachmentOpenEvent R) := by
-- proof
  apply StatMech.FrontierD.fkRectUnitAttachmentOpenEvent_dependsOnOutsideColumnBand R left right lower upper hlower

/--
[fkRectUnitAttachmentOpenEvent_mass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean)
-/
@[path]
private lemma fkRectUnitAttachmentOpenEvent_mass_pos_eq
  {R : FKRectTorus}
  {q : Real}
-- given
  (hq : 0 < q) :
-- imply
  0 < fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R) := by
-- proof
  apply StatMech.FrontierD.fkRectUnitAttachmentOpenEvent_mass_pos R hq

/--
[fkRectColumnBand_genericInter_subset_fullGraphAuxiliary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean)
-/
@[path]
private lemma fkRectColumnBand_genericInter_subset_fullGraphAuxiliary_eq
  {R : FKRectTorus}
  {right : Nat}
  {t : Finset (FKRectColumnBandVertex R 1 right 1 (R.height - 1) × FKRectColumnBandVertex R 1 right 1 (R.height - 1))} :
-- imply
  (FK.ocd_innerRestrict (Subtype.val : FKRectColumnBandVertex R 1 right 1 (R.height - 1) -> R.Vertex) ⁻¹' fkRectInducedConnectionChainEvent R (fkRectColumnBand R 1 right 1 (R.height - 1)) t) ∩ fkRectFullGraphEvent R (fkRectUnitAttachmentOpenEvent R) ⊆ fkRectFullGraphEvent R (fkRectUnitDualBarrierAuxiliary R right t) := by
-- proof
  apply StatMech.FrontierD.fkRectColumnBand_genericInter_subset_fullGraphAuxiliary R right t

/--
[fkRectColumnBand_connectionProduct_mul_attachment_le_auxiliary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean)
-/
@[path]
private lemma fkRectColumnBand_connectionProduct_mul_attachment_le_auxiliary_eq
  {R : FKRectTorus}
  {right : Nat}
  {q : Real}
  {t : Finset (FKRectColumnBandVertex R 1 right 1 (R.height - 1) × FKRectColumnBandVertex R 1 right 1 (R.height - 1))}
-- given
  (hq : 1 <= q) :
-- imply
  (∏ xy ∈ t, FK.twoPointFun (fkRectInducedGraph R (fkRectColumnBand R 1 right 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) * fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R) <= fkRectCriticalEventMass R q (fkRectUnitDualBarrierAuxiliary R right t) := by
-- proof
  apply StatMech.FrontierD.fkRectColumnBand_connectionProduct_mul_attachment_le_auxiliary R right hq t

/--
[fkRectColumnBand_attachment_mul_pow_le_auxiliary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean)
-/
@[path]
private lemma fkRectColumnBand_attachment_mul_pow_le_auxiliary_eq
  {R : FKRectTorus}
  {right blocks : Nat}
  {q a : Real}
  {t : Finset (FKRectColumnBandVertex R 1 right 1 (R.height - 1) × FKRectColumnBandVertex R 1 right 1 (R.height - 1))}
-- given
  (hq : 1 <= q)
  (ha : 0 < a)
  (ha1 : a <= 1)
  (hcard : t.card <= blocks)
  (hlower : ∀ xy ∈ t, a <= FK.twoPointFun (fkRectInducedGraph R (fkRectColumnBand R 1 right 1 (R.height - 1))) (fkRectCriticalP q) q xy.1 xy.2) :
-- imply
  fkRectCriticalEventMass R q (fkRectUnitAttachmentOpenEvent R) * a ^ blocks <= fkRectCriticalEventMass R q (fkRectUnitDualBarrierAuxiliary R right t) := by
-- proof
  apply StatMech.FrontierD.fkRectColumnBand_attachment_mul_pow_le_auxiliary R right blocks hq ha ha1 t hcard hlower

/--
[fkRectForceDualPullbackSeam_preserves_columnBand_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean)
-/
@[path]
private lemma fkRectForceDualPullbackSeam_preserves_columnBand_chain_eq
  {R : FKRectTorus}
  {left right lower upper : Nat}
  {eta omega : R.Configuration}
  {t : Finset (FKRectColumnBandVertex R left right lower upper × FKRectColumnBandVertex R left right lower upper)}
-- given
  (hlower : 1 <= lower)
  (hchain : FK.ocd_innerRestrict (Subtype.val : FKRectColumnBandVertex R left right lower upper -> R.Vertex) (fkRectFullGraphConfiguration R omega) ∈ fkRectInducedConnectionChainEvent R (fkRectColumnBand R left right lower upper) t) :
-- imply
  FK.ocd_innerRestrict (Subtype.val : FKRectColumnBandVertex R left right lower upper -> R.Vertex) (fkRectFullGraphConfiguration R (fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) eta omega)) ∈ fkRectInducedConnectionChainEvent R (fkRectColumnBand R left right lower upper) t := by
-- proof
  apply StatMech.FrontierD.fkRectForceDualPullbackSeam_preserves_columnBand_chain R left right lower upper hlower eta omega t hchain

/--
[fkRectForceDualPullbackUnitPattern_verticalWinding_of_columnBand](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean)
-/
@[path]
private lemma fkRectForceDualPullbackUnitPattern_verticalWinding_of_columnBand_eq
  {R : FKRectTorus}
  {right : Nat}
  {omega : R.Configuration}
  {t : Finset (FKRectColumnBandVertex R 1 right 1 (R.height - 1) × FKRectColumnBandVertex R 1 right 1 (R.height - 1))}
-- given
  (hright : 1 <= right)
  (hpair : (fkRectColumnBandRowOne R 1 right (fkRectUnitGapColumn R) (by rfl) hright, fkRectColumnBandLastRow R 1 right (fkRectUnitGapColumn R) (by rfl) hright) ∈ t)
  (haux : fkRectUnitDualBarrierAuxiliary R right t omega) :
-- imply
  let forced := fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))) omega forced ∈ fkRectVerticalWindingEvent R ∧ FK.ocd_innerRestrict (Subtype.val : FKRectColumnBandVertex R 1 right 1 (R.height - 1) -> R.Vertex) (fkRectFullGraphConfiguration R forced) ∈ fkRectInducedConnectionChainEvent R (fkRectColumnBand R 1 right 1 (R.height - 1)) t := by
-- proof
  apply StatMech.FrontierD.fkRectForceDualPullbackUnitPattern_verticalWinding_of_columnBand R right hright omega t hpair haux

/--
[fkRectForceDualPullbackUnitPattern_verticalWinding_of_columnBandSpans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean)
-/
@[path]
private lemma fkRectForceDualPullbackUnitPattern_verticalWinding_of_columnBandSpans_eq
  {R : FKRectTorus}
  {right : Nat}
  {omega : R.Configuration}
  {t : Finset (FKRectColumnBandVertex R 1 right 1 (R.height - 1) × FKRectColumnBandVertex R 1 right 1 (R.height - 1))}
-- given
  (hright : 1 <= right)
  (hspans : FKRectColumnBandConnectionChainSpans R 1 right (fkRectUnitGapColumn R) (by rfl) hright t)
  (haux : fkRectUnitDualBarrierAuxiliary R right t omega) :
-- imply
  let forced := fkRectForceIndexedPattern R (fkRectDualPullbackIndexSet R (fkRectHorizontalCutEdges R)) (fkRectDualPullbackConfiguration R (fkRectAllButOneOpenConfiguration R (fkRectUnitLeftBarrierGap R))) omega forced ∈ fkRectVerticalWindingEvent R ∧ FK.ocd_innerRestrict (Subtype.val : FKRectColumnBandVertex R 1 right 1 (R.height - 1) -> R.Vertex) (fkRectFullGraphConfiguration R forced) ∈ fkRectInducedConnectionChainEvent R (fkRectColumnBand R 1 right 1 (R.height - 1)) t := by
-- proof
  apply StatMech.FrontierD.fkRectForceDualPullbackUnitPattern_verticalWinding_of_columnBandSpans R right hright omega t hspans haux


-- created on 2026-10-23
