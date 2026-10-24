import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKRectDiagonalBlockLower
open StatMech StatMech.FrontierD


/--
[exists_fkRectRightBand_verticalWalk_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma exists_fkRectRightBand_verticalWalk_length_eq
  {R : FKRectTorus}
  {cut : Nat}
  {x : Fin R.width}
  {r n : Nat}
-- given
  (hx : cut <= x.val)
  (hr : 1 <= r)
  (hupper : r + n <= R.height - 1) :
-- imply
  ∃ w : (fkRectInducedGraph R (fkRectRightStripBand R cut 1 (R.height - 1))).Walk (fkRectRightBandVertexAtRow R cut x hx r ⟨hr, by omega⟩) (fkRectRightBandVertexAtRow R cut x hx (r + n) ⟨by omega, hupper⟩), w.length = n := by
-- proof
  apply StatMech.FrontierD.exists_fkRectRightBand_verticalWalk_length R cut x hx r n hr hupper

/--
[fkRectWindingBlock_twoPoint_ge_cFE_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma fkRectWindingBlock_twoPoint_ge_cFE_pow_eq
  {q : Real}
  {k scale blocks cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
  {i : Fin (blocks + 1)}
-- given
  (hq : 1 <= q)
  (hx : cut <= x.val) :
-- imply
  FK.cFE (fkRectCriticalP q) q ^ (2 * (scale + 1)) <= FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectRightStripBand (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc) (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ) := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_twoPoint_ge_cFE_pow hq k scale blocks cut x hx i

/--
[fkRectWindingBlockBadIndices_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma fkRectWindingBlockBadIndices_card_le_eq
  {blocks m : Nat} :
-- imply
  (fkRectWindingBlockBadIndices blocks m).card <= 2 * m := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlockBadIndices_card_le blocks m

/--
[not_mem_fkRectWindingBlockBadIndices](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma not_mem_fkRectWindingBlockBadIndices_eq
  {blocks m : Nat}
  {i : Fin (blocks + 1)}
-- given
  (hi : i ∉ fkRectWindingBlockBadIndices blocks m) :
-- imply
  m <= i.val ∧ m <= blocks - i.val := by
-- proof
  apply StatMech.FrontierD.not_mem_fkRectWindingBlockBadIndices i hi

/--
[fkRectWindingBlock_connectionProduct_ge_of_bulk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma fkRectWindingBlock_connectionProduct_ge_of_bulk_eq
  {q a : Real}
  {m k scale blocks cut : Nat}
  {x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width}
-- given
  (hq : 1 <= q)
  (ha : 0 < a)
  (ha1 : a <= 1)
  (hx : cut <= x.val)
  (hbulk : ∀ i : Fin (blocks + 1), i ∉ fkRectWindingBlockBadIndices blocks m -> a <= FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectRightStripBand (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc) (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ)) :
-- imply
  (FK.cFE (fkRectCriticalP q) q ^ (2 * (scale + 1))) ^ (2 * m) * a ^ (blocks + 1) <= ∏ xy ∈ connectionPathPairs (blocks + 1) (fkRectWindingBlockPathVertex k scale blocks cut x hx), FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectRightStripBand (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q xy.1 xy.2 := by
-- proof
  apply StatMech.FrontierD.fkRectWindingBlock_connectionProduct_ge_of_bulk hq ha ha1 m k scale blocks cut x hx hbulk

/--
[exists_margin_criticalDiagonal_lt_windingBlock_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma exists_margin_criticalDiagonal_lt_windingBlock_twoPoint_eq
  {q : Real}
  {scale : Nat}
  {epsilon : Real}
-- given
  (hq : 4 < q)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ m : Nat, scale + 1 <= m ∧ ∀ (k blocks cut : Nat) (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width) (hx : cut <= x.val) (i : Fin (blocks + 1)), 1 <= cut -> cut + 2 * m <= x.val -> x.val + 2 * m < (fkRectWindingBlockVerticalFamily k scale blocks).width -> 1 + 2 * m <= (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc).1.2.val -> (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc).1.2.val + 2 * m <= (fkRectWindingBlockVerticalFamily k scale blocks).height - 1 -> fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1) - epsilon < FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectRightStripBand (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q (fkRectWindingBlockPathVertex k scale blocks cut x hx i.castSucc) (fkRectWindingBlockPathVertex k scale blocks cut x hx i.succ) := by
-- proof
  apply StatMech.FrontierD.exists_margin_criticalDiagonal_lt_windingBlock_twoPoint hq scale hepsilon

/--
[exists_margin_windingBlock_connectionProduct_ge_diagonal_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma exists_margin_windingBlock_connectionProduct_ge_diagonal_sub_eq
  {q : Real}
  {scale : Nat}
  {epsilon : Real}
-- given
  (hq : 4 < q)
  (hepsilon : 0 < epsilon)
  (hepsilonLt : epsilon < fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) :
-- imply
  ∃ m : Nat, scale + 1 <= m ∧ ∀ (k blocks cut : Nat) (x : Fin (fkRectWindingBlockVerticalFamily k scale blocks).width) (hx : cut <= x.val), 1 <= cut -> cut + 2 * m <= x.val -> x.val + 2 * m < (fkRectWindingBlockVerticalFamily k scale blocks).width -> (FK.cFE (fkRectCriticalP q) q ^ (2 * (scale + 1))) ^ (2 * m) * (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1) - epsilon) ^ (blocks + 1) <= ∏ xy ∈ connectionPathPairs (blocks + 1) (fkRectWindingBlockPathVertex k scale blocks cut x hx), FK.twoPointFun (fkRectInducedGraph (fkRectWindingBlockVerticalFamily k scale blocks) (fkRectRightStripBand (fkRectWindingBlockVerticalFamily k scale blocks) cut 1 ((fkRectWindingBlockVerticalFamily k scale blocks).height - 1))) (fkRectCriticalP q) q xy.1 xy.2 := by
-- proof
  apply StatMech.FrontierD.exists_margin_windingBlock_connectionProduct_ge_diagonal_sub hq scale hepsilon hepsilonLt

/--
[eventually_fkRectWindingBlock_chargeOneRate_le_diagonalSub_add_barrier_of_leftRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma eventually_fkRectWindingBlock_chargeOneRate_le_diagonalSub_add_barrier_of_leftRight_eq
  {q : Real}
  {scale leftRight : Nat}
  {epsilon barrierUpper : Real}
-- given
  (hq : 4 < q)
  (hone : 1 <= leftRight)
  (hepsilon : 0 < epsilon)
  (hepsilonLt : epsilon < fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1))
  (hbarrier : ∀ᶠ k in Filter.atTop, ∀ delta : Real, 0 < delta -> ∀ᶠ blocks in Filter.atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height <= barrierUpper + delta) :
-- imply
  ∀ᶠ k in Filter.atTop, -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1) - epsilon) / (2 * (scale + 1) : Real) + barrierUpper := by
-- proof
  apply StatMech.FrontierD.eventually_fkRectWindingBlock_chargeOneRate_le_diagonalSub_add_barrier_of_leftRight hq scale leftRight hone hepsilon hepsilonLt hbarrier

/--
[eventually_fkRectWindingBlock_chargeOneRate_le_diagonalSub_add_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma eventually_fkRectWindingBlock_chargeOneRate_le_diagonalSub_add_barrier_eq
  {q : Real}
  {scale : Nat}
  {epsilon barrierUpper : Real}
-- given
  (hq : 4 < q)
  (hepsilon : 0 < epsilon)
  (hepsilonLt : epsilon < fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1))
  (hbarrier : ∀ᶠ k in Filter.atTop, ∀ delta : Real, 0 < delta -> ∀ᶠ blocks in Filter.atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) 1 (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height <= barrierUpper + delta) :
-- imply
  ∀ᶠ k in Filter.atTop, -sixVertexFixedChargeLogRatio (fkQgt4SixVertexWeight q) 1 (k + 1) <= -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1) - epsilon) / (2 * (scale + 1) : Real) + barrierUpper := by
-- proof
  apply StatMech.FrontierD.eventually_fkRectWindingBlock_chargeOneRate_le_diagonalSub_add_barrier hq scale hepsilon hepsilonLt hbarrier

/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier_of_leftRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier_of_leftRight_eq
  {q : Real}
  {scale leftRight : Nat}
  {barrierUpper : Real}
-- given
  (hq : 4 < q)
  (hone : 1 <= leftRight)
  (hbarrier : ∀ᶠ k in Filter.atTop, ∀ delta : Real, 0 < delta -> ∀ᶠ blocks in Filter.atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) leftRight (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height <= barrierUpper + delta) :
-- imply
  fkQgt4SixVertexGapRate q <= -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) / (2 * (scale + 1) : Real) + barrierUpper := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier_of_leftRight hq scale leftRight hone hbarrier

/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier_eq
  {q : Real}
  {scale : Nat}
  {barrierUpper : Real}
-- given
  (hq : 4 < q)
  (hbarrier : ∀ᶠ k in Filter.atTop, ∀ delta : Real, 0 < delta -> ∀ᶠ blocks in Filter.atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) 1 (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height <= barrierUpper + delta) :
-- imply
  fkQgt4SixVertexGapRate q <= -Real.log (fkQgt4CriticalFreeExactDiagonalTwoPoint hq (scale + 1)) / (2 * (scale + 1) : Real) + barrierUpper := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalfScale_add_barrier hq scale hbarrier

/--
[fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_leftBarrierBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDiagonalBlockLower.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_leftBarrierBounds_eq
  {q : Real}
-- given
  (hq : 4 < q)
  (leftRight : Nat -> Nat)
  (hone : forall scale, 1 <= leftRight scale)
  (barrierUpper : Nat -> Real)
  (hbarrierUpper : Tendsto barrierUpper Filter.atTop (nhds 0))
  (hbarrier : forall scale, ∀ᶠ k in Filter.atTop, ∀ delta : Real, 0 < delta -> ∀ᶠ blocks in Filter.atTop, -Real.log (fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectSourceLeftBarrier (fkRectWindingBlockVerticalFamily k scale blocks) (leftRight scale) (fkRectUnitLeftBarrierGap (fkRectWindingBlockVerticalFamily k scale blocks)))) / (fkRectWindingBlockVerticalFamily k scale blocks).height <= barrierUpper scale + delta) :
-- imply
  fkQgt4SixVertexGapRate q <= fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2 := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_le_exactDiagonalHalf_of_leftBarrierBounds hq leftRight hone barrierUpper hbarrierUpper hbarrier


-- created on 2026-10-23
