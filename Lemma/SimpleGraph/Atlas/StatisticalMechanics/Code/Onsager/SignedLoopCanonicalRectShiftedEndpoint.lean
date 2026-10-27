import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
open MeasureTheory Filter Topology StatMech StatMech.Onsager


/--
[ons_originPositiveBoxVertex_ne_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_originPositiveBoxVertex_ne_neighbor_eq
  {n : Nat} :
-- imply
  ons_originPositiveBoxVertex n ≠ ons_neighborPositiveBoxVertex n := by
-- proof
  apply StatMech.Onsager.ons_originPositiveBoxVertex_ne_neighbor n

/--
[ons_originPositiveBoxVertex_adj_neighbor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_originPositiveBoxVertex_adj_neighbor_eq
  {n : Nat} :
-- imply
  (sctBoxGraph 2 (n + 1)).Adj (ons_originPositiveBoxVertex n) (ons_neighborPositiveBoxVertex n) := by
-- proof
  apply StatMech.Onsager.ons_originPositiveBoxVertex_adj_neighbor n

/--
[ons_originNeighborRectDualPath_source_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_originNeighborRectDualPath_source_pullback_eq
  {n : Nat} :
-- imply
  ((ons_box2EquivRect (n + 1)).symm (ons_originNeighborRectDualPath n).source).1 = (![0, 0] : Site 2) := by
-- proof
  apply StatMech.Onsager.ons_originNeighborRectDualPath_source_pullback n

/--
[ons_originNeighborRectDualPath_target_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_originNeighborRectDualPath_target_pullback_eq
  {n : Nat} :
-- imply
  ((ons_box2EquivRect (n + 1)).symm (ons_originNeighborRectDualPath n).target).1 = (![1, 0] : Site 2) := by
-- proof
  apply StatMech.Onsager.ons_originNeighborRectDualPath_target_pullback n

/--
[ons_fixedPairRectDualPath_source_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_fixedPairRectDualPath_source_eventually_eq
  {N : Nat}
  {a b : Site 2}
-- given
  (ha : a ∈ box 2 N)
  (hb : b ∈ box 2 N)
  (hab : a ≠ b) :
-- imply
  ∀ᶠ n in atTop, ((ons_box2EquivRect (n + 1)).symm (ons_fixedPairRectDualPath N a b ha hb hab n).source).1 = a := by
-- proof
  apply StatMech.Onsager.ons_fixedPairRectDualPath_source_eventually N a b ha hb hab

/--
[ons_fixedPairRectDualPath_target_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_fixedPairRectDualPath_target_eventually_eq
  {N : Nat}
  {a b : Site 2}
-- given
  (ha : a ∈ box 2 N)
  (hb : b ∈ box 2 N)
  (hab : a ≠ b) :
-- imply
  ∀ᶠ n in atTop, ((ons_box2EquivRect (n + 1)).symm (ons_fixedPairRectDualPath N a b ha hb hab n).target).1 = b := by
-- proof
  apply StatMech.Onsager.ons_fixedPairRectDualPath_target_eventually N a b ha hb hab

/--
[ons_canonicalRectDualPathRatio_shifted_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_canonicalRectDualPathRatio_shifted_tendsto_freeState_eq
  {beta : Real}
  {a b : Site 2}
-- given
  (hbeta : 0 < beta)
  (path : ∀ n, ons_RectDualPath (2 * (n + 1)) (2 * (n + 1)))
  (hsource : ∀ᶠ n in atTop, ((ons_box2EquivRect (n + 1)).symm (path n).source).1 = a)
  (htarget : ∀ᶠ n in atTop, ((ons_box2EquivRect (n + 1)).symm (path n).target).1 = b) :
-- imply
  Tendsto (fun n => ons_rectDualPathRatio (ons_rectDualStraightLineEmbedding (2 * (n + 1)) (2 * (n + 1))) (path n) beta) atTop (nhds ((((∫ spin, spinProd {a, b} spin ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_canonicalRectDualPathRatio_shifted_tendsto_freeState beta hbeta path a b hsource htarget

/--
[ons_originNeighborRectDualPathRatio_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_originNeighborRectDualPathRatio_tendsto_freeState_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Tendsto (fun n => ons_rectDualPathRatio (ons_rectDualStraightLineEmbedding (2 * (n + 1)) (2 * (n + 1))) (ons_originNeighborRectDualPath n) beta) atTop (nhds ((((∫ spin, spinProd {(![0, 0] : Site 2), (![1, 0] : Site 2)} spin ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_originNeighborRectDualPathRatio_tendsto_freeState beta hbeta

/--
[ons_fixedPairRectDualPathRatio_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_fixedPairRectDualPathRatio_tendsto_freeState_eq
  {beta : Real}
  {N : Nat}
  {a b : Site 2}
-- given
  (hbeta : 0 < beta)
  (ha : a ∈ box 2 N)
  (hb : b ∈ box 2 N)
  (hab : a ≠ b) :
-- imply
  Tendsto (fun n => ons_rectDualPathRatio (ons_rectDualStraightLineEmbedding (2 * (n + 1)) (2 * (n + 1))) (ons_fixedPairRectDualPath N a b ha hb hab n) beta) atTop (nhds ((((∫ spin, spinProd {a, b} spin ∂(freeState 2 beta 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_fixedPairRectDualPathRatio_tendsto_freeState beta hbeta N a b ha hb hab

/--
[ons_canonicalRectDualPathCriticalRatio_shifted_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_canonicalRectDualPathCriticalRatio_shifted_tendsto_freeState_eq
  {a b : Site 2}
-- given
  (path : ∀ n, ons_RectDualPath (2 * (n + 1)) (2 * (n + 1)))
  (hsource : ∀ᶠ n in atTop, ((ons_box2EquivRect (n + 1)).symm (path n).source).1 = a)
  (htarget : ∀ᶠ n in atTop, ((ons_box2EquivRect (n + 1)).symm (path n).target).1 = b) :
-- imply
  Tendsto (fun n => ons_rectDualPathCriticalRatio (ons_rectDualStraightLineEmbedding (2 * (n + 1)) (2 * (n + 1))) (path n)) atTop (nhds ((((∫ spin, spinProd {a, b} spin ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_canonicalRectDualPathCriticalRatio_shifted_tendsto_freeState path a b hsource htarget

/--
[ons_originNeighborRectDualPathCriticalRatio_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_originNeighborRectDualPathCriticalRatio_tendsto_freeState_eq :
-- imply
  Tendsto (fun n => ons_rectDualPathCriticalRatio (ons_rectDualStraightLineEmbedding (2 * (n + 1)) (2 * (n + 1))) (ons_originNeighborRectDualPath n)) atTop (nhds ((((∫ spin, spinProd {(![0, 0] : Site 2), (![1, 0] : Site 2)} spin ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_originNeighborRectDualPathCriticalRatio_tendsto_freeState

/--
[ons_fixedPairRectDualPathCriticalRatio_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopCanonicalRectShiftedEndpoint.lean)
-/
@[path]
private lemma ons_fixedPairRectDualPathCriticalRatio_tendsto_freeState_eq
  {N : Nat}
  {a b : Site 2}
-- given
  (ha : a ∈ box 2 N)
  (hb : b ∈ box 2 N)
  (hab : a ≠ b) :
-- imply
  Tendsto (fun n => ons_rectDualPathCriticalRatio (ons_rectDualStraightLineEmbedding (2 * (n + 1)) (2 * (n + 1))) (ons_fixedPairRectDualPath N a b ha hb hab n)) atTop (nhds ((((∫ spin, spinProd {a, b} spin ∂(freeState 2 ons_betaC 0 : Measure (ConfigSpace (Site 2)))) : Real) : Complex) ^ 2)) := by
-- proof
  apply StatMech.Onsager.ons_fixedPairRectDualPathCriticalRatio_tendsto_freeState N a b ha hb hab


-- created on 2026-10-23
