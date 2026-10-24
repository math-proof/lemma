import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexUniformCentralPressure
open Finset Matrix Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexSectorTrace_particleHole_uniformPressure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma sixVertexSectorTrace_particleHole_uniformPressure_eq
  {N n : Nat}
  {M : Nat}
  {c : Real}
-- given
  (hn : n <= N) :
-- imply
  Matrix.trace (sixVertexSectorTransfer N (N - n) c ^ M) = Matrix.trace (sixVertexSectorTransfer N n c ^ M) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_particleHole_uniformPressure hn M c

/--
[sixVertexCentralTrace_le_fixedWidthPartitionSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma sixVertexCentralTrace_le_fixedWidthPartitionSum_eq
  {N M : Nat}
  {c : Real}
-- given
  (hM : 0 < M)
  (hc : 0 < c) :
-- imply
  Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ M) <= sixVertexFixedWidthPartitionSum N M c := by
-- proof
  apply StatMech.FrontierD.sixVertexCentralTrace_le_fixedWidthPartitionSum N M hM hc

/--
[sixVertexBalancedTraceShare_mem_Ioc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma sixVertexBalancedTraceShare_mem_Ioc_eq
  {N M : Nat}
  {c : Real}
-- given
  (hM : 0 < M)
  (hc : 0 < c) :
-- imply
  sixVertexBalancedTraceShare N M c ∈ Set.Ioc 0 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexBalancedTraceShare_mem_Ioc N M hM hc

/--
[sixVertexAllHeightCentralTraceMaximal_of_traceLogConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma sixVertexAllHeightCentralTraceMaximal_of_traceLogConcave_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : Even N)
  (hc : 0 < c)
  (hlc : SixVertexSectorTraceLogConcave N c) :
-- imply
  SixVertexAllHeightCentralTraceMaximal N c := by
-- proof
  apply StatMech.FrontierD.sixVertexAllHeightCentralTraceMaximal_of_traceLogConcave N hN hc hlc

/--
[sixVertexUniformHeightCentralTraceBound_of_allHeightCentralTraceMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma sixVertexUniformHeightCentralTraceBound_of_allHeightCentralTraceMaximal_eq
  {N : Nat}
  {c : Real}
-- given
  (hmax : SixVertexAllHeightCentralTraceMaximal N c) :
-- imply
  SixVertexUniformHeightCentralTraceBound N c := by
-- proof
  apply StatMech.FrontierD.sixVertexUniformHeightCentralTraceBound_of_allHeightCentralTraceMaximal N hmax

/--
[sixVertexUniformHeightCentralTraceBound_of_traceLogConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma sixVertexUniformHeightCentralTraceBound_of_traceLogConcave_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : Even N)
  (hc : 0 < c)
  (hlc : SixVertexSectorTraceLogConcave N c) :
-- imply
  SixVertexUniformHeightCentralTraceBound N c := by
-- proof
  apply StatMech.FrontierD.sixVertexUniformHeightCentralTraceBound_of_traceLogConcave N hN hc hlc

/--
[sixVertexPositiveEvenHeightCentralTraceMaximal_of_traceLogConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma sixVertexPositiveEvenHeightCentralTraceMaximal_of_traceLogConcave_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : Even N)
  (hc : 0 < c)
  (hlc : SixVertexSectorPositiveEvenTraceLogConcave N c) :
-- imply
  SixVertexPositiveEvenHeightCentralTraceMaximal N c := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveEvenHeightCentralTraceMaximal_of_traceLogConcave N hN hc hlc

/--
[sixVertexPositiveEvenHeight_full_le_card_mul_central_of_traceLogConcave](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma sixVertexPositiveEvenHeight_full_le_card_mul_central_of_traceLogConcave_eq
  {N : Nat}
  {c : Real}
  {M : Nat}
-- given
  (hN : Even N)
  (hc : 0 < c)
  (hlc : SixVertexSectorPositiveEvenTraceLogConcave N c) :
-- imply
  sixVertexFixedWidthPartitionSum N (sixVertexPositiveEvenHeight M) c <= (N + 1 : Nat) * Matrix.trace (sixVertexSectorTransfer N (N / 2) c ^ sixVertexPositiveEvenHeight M) := by
-- proof
  apply StatMech.FrontierD.sixVertexPositiveEvenHeight_full_le_card_mul_central_of_traceLogConcave N hN hc hlc M

/--
[sixVertexWidthTopEigenvalue_eq_halfFilled_of_uniformHeightCentralTraceBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma sixVertexWidthTopEigenvalue_eq_halfFilled_of_uniformHeightCentralTraceBound_eq
  {N : Nat}
  {c : Real}
-- given
  (hN : Even N)
  (hc : 0 < c)
  (hbound : SixVertexUniformHeightCentralTraceBound N c) :
-- imply
  sixVertexWidthTopEigenvalue N c = sixVertexSectorTopEigenvalue N (N / 2) (Nat.div_le_self N 2) c := by
-- proof
  apply StatMech.FrontierD.sixVertexWidthTopEigenvalue_eq_halfFilled_of_uniformHeightCentralTraceBound N hN hc hbound

/--
[fkRectBalancedShareSpectralGap_eq_zero_of_uniformHeightCentralTraceBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma fkRectBalancedShareSpectralGap_eq_zero_of_uniformHeightCentralTraceBound_eq
  {q : Real}
  {r k : Nat}
-- given
  (hq : 4 < q)
  (hbound : SixVertexUniformHeightCentralTraceBound (sixVertexFourWidth r (k + 1)) (fkQgt4SixVertexWeight q)) :
-- imply
  fkRectBalancedShareSpectralGap q r k = 0 := by
-- proof
  apply StatMech.FrontierD.fkRectBalancedShareSpectralGap_eq_zero_of_uniformHeightCentralTraceBound hq r k hbound

/--
[tendsto_fkRectBalancedShareSpectralGap_zero_of_uniformHeightCentralTraceBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma tendsto_fkRectBalancedShareSpectralGap_zero_of_uniformHeightCentralTraceBound_eq
  {q : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hbound : SixVertexCanonicalUniformHeightCentralTraceBound q) :
-- imply
  Tendsto (fkRectBalancedShareSpectralGap q r) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectBalancedShareSpectralGap_zero_of_uniformHeightCentralTraceBound hq r hbound

/--
[tendsto_fkRectBalancedNormalizationRate_zero_of_crossingFloor_uniformTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma tendsto_fkRectBalancedNormalizationRate_zero_of_crossingFloor_uniformTrace_eq
  {q hardFloor : Real}
  {r : Nat}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hbound : SixVertexCanonicalUniformHeightCentralTraceBound q) :
-- imply
  Tendsto (fkRectBalancedSectorNormalizationVerticalRate hq r) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_fkRectBalancedNormalizationRate_zero_of_crossingFloor_uniformTrace hq hhard hcross r hbound

/--
[fkQgt4_windingBridge_of_crossingFloor_uniformCentralTrace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexUniformCentralPressure.lean)
-/
@[path]
private lemma fkQgt4_windingBridge_of_crossingFloor_uniformCentralTrace_eq
  {q hardFloor : Real}
-- given
  (hq : 4 < q)
  (hhard : 0 < hardFloor)
  (hcross : forall scale k : Nat, 0 < scale -> Even scale -> 12 * scale + 2 < 2 * (k + 3) -> ∀ᶠ blocks in atTop, hardFloor <= fkRectCriticalEventMass (fkRectWindingBlockVerticalFamily k scale blocks) q (fkRectDevelopedRectangleHorizontalCrossingEvent (fkRectWindingBlockVerticalFamily k scale blocks) scale 0 (2 * (scale : Int)) 0 scale))
  (hbound : SixVertexCanonicalUniformHeightCentralTraceBound q) :
-- imply
  FKQgt4TorusSixVertexWindingBridge (fkQgt4CriticalFreeExactDiagonalRateLimit hq / 2) (fkQgt4SixVertexGapRate q) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_windingBridge_of_crossingFloor_uniformCentralTrace hq hhard hcross hbound


-- created on 2026-10-23
