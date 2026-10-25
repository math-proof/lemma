import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInternalCylinderLimit.Part5
open MeasureTheory Filter Topology StatMech StatMech.FrontierA


/--
[internalCentralVertexEmbedding_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma internalCentralVertexEmbedding_none_eq
  {n m : Nat}
-- given
  (hnm : centralSquareSide n < m) :
-- imply
  internalCentralVertexEmbedding n m hnm none = none := by
-- proof
  apply StatMech.FrontierA.internalCentralVertexEmbedding_none n m hnm

/--
[internalCentralVertexEmbedding_some](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma internalCentralVertexEmbedding_some_eq
  {n m : Nat}
  {q : CubicalCell (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n)}
-- given
  (hnm : centralSquareSide n < m) :
-- imply
  internalCentralVertexEmbedding n m hnm (some q) = some (internalCentralCellEmbedding n m hnm q) := by
-- proof
  apply StatMech.FrontierA.internalCentralVertexEmbedding_some n m hnm q

/--
[oddCubicalCenteredSite_internalCentralCellEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma oddCubicalCenteredSite_internalCentralCellEmbedding_eq
  {n m : Nat}
  {q : CubicalCell (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n)}
-- given
  (hnm : centralSquareSide n < m) :
-- imply
  oddCubicalCenteredSite m (internalCentralCellEmbedding n m hnm q) = centralCylinderSite n q := by
-- proof
  apply StatMech.FrontierA.oddCubicalCenteredSite_internalCentralCellEmbedding n m hnm q

/--
[cubicalDualL1_internalCentralVertexEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma cubicalDualL1_internalCentralVertexEmbedding_eq
  {n m : Nat}
  {u v : CubicalDualVertex (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n)}
-- given
  (hnm : centralSquareSide n < m) :
-- imply
  cubicalDualL1 (internalCentralVertexEmbedding n m hnm u) (internalCentralVertexEmbedding n m hnm v) = cubicalDualL1 u v := by
-- proof
  apply StatMech.FrontierA.cubicalDualL1_internalCentralVertexEmbedding n m hnm u v

/--
[mem_centralLowerBoundaryVertices_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma mem_centralLowerBoundaryVertices_iff_eq
  {n : Nat}
  {q : CubicalCell (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n)} :
-- imply
  some q ∈ centralLowerBoundaryVertices n ↔ q.z.val < centralSquareSide n ∧ (q.x.val = 0 ∨ q.x.val + 1 = centralSquareSide n ∨ q.y.val = 0 ∨ q.y.val + 1 = centralSquareSide n ∨ q.z.val = 0) := by
-- proof
  apply StatMech.FrontierA.mem_centralLowerBoundaryVertices_iff n q

/--
[centralLowerBoundaryVertices_map_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma centralLowerBoundaryVertices_map_internal_eq
  {n m : Nat}
-- given
  (hnm : centralSquareSide n < m) :
-- imply
  (centralLowerBoundaryVertices n).map (internalCentralVertexEmbedding n m hnm) = cubicalInternalCentralBoundaryVertices (centralSquareSide n) m := by
-- proof
  apply StatMech.FrontierA.centralLowerBoundaryVertices_map_internal n m hnm

/--
[centralUpperLayerVertices_map_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma centralUpperLayerVertices_map_internal_eq
  {n m : Nat}
-- given
  (hnm : centralSquareSide n < m) :
-- imply
  (centralUpperLayerVertices n).map (internalCentralVertexEmbedding n m hnm) = cubicalInternalCentralUpperCoordinateVertices (centralSquareSide n) m hnm.le := by
-- proof
  apply StatMech.FrontierA.centralUpperLayerVertices_map_internal n m hnm

/--
[centralCylinderPairs_map_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma centralCylinderPairs_map_internal_eq
  {n m : Nat}
-- given
  (hnm : centralSquareSide n < m) :
-- imply
  (centralCylinderPairs n).map ((internalCentralVertexEmbedding n m hnm).prodMap (internalCentralVertexEmbedding n m hnm)) = (cubicalInternalCentralBoundaryVertices (centralSquareSide n) m).product (cubicalInternalCentralUpperVertices (centralSquareSide n) m hnm.le) := by
-- proof
  apply StatMech.FrontierA.centralCylinderPairs_map_internal n m hnm

/--
[cubicalInternalCentralWilsonExpectation_ge_fixed_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma cubicalInternalCentralWilsonExpectation_ge_fixed_product_eq
  {n m : Nat}
  {K : Real}
-- given
  (hnm : centralSquareSide n < m)
  (hK : 0 < K) :
-- imply
  (∏ uv ∈ centralCylinderPairs n, (1 - multibondIsingTwoPoint cubicalDualEnds (fun _ : CubicalPlaquette (oddCubeSide m) (oddCubeSide m) (oddCubeSide m) => gaugeDualCoupling K) (internalCentralVertexEmbedding n m hnm uv.1) (internalCentralVertexEmbedding n m hnm uv.2))) <= gaugeWilsonExpectation cubicalPlaquetteIncidence (fun _ => K) (gaugeSurfaceBoundary cubicalPlaquetteIncidence (cubicalInternalCentralSheet (centralSquareSide n) m hnm.le)) := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentralWilsonExpectation_ge_fixed_product n m hnm K hK

/--
[exists_internalCentralPairCorrelation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma exists_internalCentralPairCorrelation_tendsto_eq
  {beta : Real}
  {n : Nat} :
-- imply
  ∃ m : Nat -> Nat, ∃ hm : ∀ k, centralSquareSide n < m k, Tendsto m atTop atTop ∧ ∀ uv, uv ∈ centralCylinderPairs n -> Tendsto (fun k => internalCentralPairCorrelation beta n (m k) (hm k) uv) atTop (nhds (plusCorr 3 beta (centralCylinderVertexSite n uv.1) (centralCylinderVertexSite n uv.2))) := by
-- proof
  apply StatMech.FrontierA.exists_internalCentralPairCorrelation_tendsto beta n

/--
[exists_internalCentralCylinderProduct_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma exists_internalCentralCylinderProduct_tendsto_eq
  {beta : Real}
  {n : Nat} :
-- imply
  ∃ m : Nat -> Nat, ∃ hm : ∀ k, centralSquareSide n < m k, Tendsto m atTop atTop ∧ Tendsto (fun k => ∏ uv ∈ centralCylinderPairs n, (1 - internalCentralPairCorrelation beta n (m k) (hm k) uv)) atTop (nhds (∏ uv ∈ centralCylinderPairs n, (1 - plusCorr 3 beta (centralCylinderVertexSite n uv.1) (centralCylinderVertexSite n uv.2)))) := by
-- proof
  apply StatMech.FrontierA.exists_internalCentralCylinderProduct_tendsto beta n

/--
[cubicalInternalCentralSheet_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma cubicalInternalCentralSheet_eq_map_eq
  {n m : Nat}
-- given
  (hnm : centralSquareSide n <= m) :
-- imply
  cubicalInternalCentralSheet (centralSquareSide n) m hnm = (cubicalXYSheet (a := centralSquareSide n) (b := centralSquareSide n) (c := 0) (0 : Fin 1)).map (cubicalPlaquetteChart m m m (by dsimp [oddCubeSide, centralSquareSide] at *; omega) (by dsimp [oddCubeSide, centralSquareSide] at *; omega) (by dsimp [oddCubeSide]; omega)) := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentralSheet_eq_map n m hnm

/--
[gaugeSurfaceBoundary_cubicalInternalCentralSheet_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma gaugeSurfaceBoundary_cubicalInternalCentralSheet_fixed_eq
  {n m : Nat}
-- given
  (hnm : centralSquareSide n <= m) :
-- imply
  gaugeSurfaceBoundary cubicalPlaquetteIncidence (cubicalInternalCentralSheet (centralSquareSide n) m hnm) = (cubicalXYLoop (a := centralSquareSide n) (b := centralSquareSide n) (c := 0) (0 : Fin 1)).map (cubicalEdgeChart m m m (by dsimp [oddCubeSide, centralSquareSide] at *; omega) (by dsimp [oddCubeSide, centralSquareSide] at *; omega) (by dsimp [oddCubeSide]; omega)) := by
-- proof
  apply StatMech.FrontierA.gaugeSurfaceBoundary_cubicalInternalCentralSheet_fixed n m hnm

/--
[cubicalInternalCentralWilsonExpectation_le_fixed_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma cubicalInternalCentralWilsonExpectation_le_fixed_succ_eq
  {K : Real}
  {n m : Nat}
-- given
  (hK : 0 <= K)
  (hnm : centralSquareSide n <= m) :
-- imply
  cubicalInternalCentralWilsonExpectation K n m hnm <= cubicalFixedLoopWilsonSequence K (centralSquareSide n) (centralSquareSide n) (m + 1) := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentralWilsonExpectation_le_fixed_succ hK n m hnm

/--
[cubicalFixedLoopWilsonSequence_le_internal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma cubicalFixedLoopWilsonSequence_le_internal_eq
  {K : Real}
  {n t m : Nat}
-- given
  (hK : 0 <= K)
  (hnm : centralSquareSide n <= m)
  (htm : t + centralSquareSide n <= m + 1) :
-- imply
  cubicalFixedLoopWilsonSequence K (centralSquareSide n) (centralSquareSide n) t <= cubicalInternalCentralWilsonExpectation K n m hnm := by
-- proof
  apply StatMech.FrontierA.cubicalFixedLoopWilsonSequence_le_internal hK n t m hnm htm

/--
[cubicalInternalCentralWilsonExpectation_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma cubicalInternalCentralWilsonExpectation_tendsto_eq
  {K : Real}
  {n : Nat}
-- given
  (hK : 0 < K)
  (m : Nat -> Nat)
  (hm : ∀ k, centralSquareSide n <= m k)
  (hmTop : Tendsto m atTop atTop) :
-- imply
  Tendsto (fun k => cubicalInternalCentralWilsonExpectation K n (m k) (hm k)) atTop (nhds (cubicalInfiniteVolumeWilsonExpectation K (centralSquareSide n) (centralSquareSide n))) := by
-- proof
  apply StatMech.FrontierA.cubicalInternalCentralWilsonExpectation_tendsto hK n m hm hmTop

/--
[centralCylinderPlusCorrProduct_le_infiniteWilson](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma centralCylinderPlusCorrProduct_le_infiniteWilson_eq
  {K : Real}
  {n : Nat}
-- given
  (hK : 0 < K) :
-- imply
  (∏ uv ∈ centralCylinderPairs n, (1 - plusCorr 3 (gaugeDualCoupling K) (centralCylinderVertexSite n uv.1) (centralCylinderVertexSite n uv.2))) <= cubicalInfiniteVolumeWilsonExpectation K (centralSquareSide n) (centralSquareSide n) := by
-- proof
  apply StatMech.FrontierA.centralCylinderPlusCorrProduct_le_infiniteWilson K hK n

/--
[l1dist_centralCylinderVertexSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma l1dist_centralCylinderVertexSite_eq
  {n : Nat}
  {uv : CubicalDualVertex (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n) × CubicalDualVertex (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n)}
-- given
  (huv : uv ∈ centralCylinderPairs n) :
-- imply
  l1dist 3 (centralCylinderVertexSite n uv.1) (centralCylinderVertexSite n uv.2) = cubicalDualL1 uv.1 uv.2 := by
-- proof
  apply StatMech.FrontierA.l1dist_centralCylinderVertexSite n uv huv

/--
[centralCylinderPairs_l1_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma centralCylinderPairs_l1_ge_one_eq
  {n : Nat}
  {uv : CubicalDualVertex (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n) × CubicalDualVertex (centralSquareSide n) (centralSquareSide n) (centralSquareSide n + centralSquareSide n)}
-- given
  (huv : uv ∈ centralCylinderPairs n) :
-- imply
  (1 : Real) <= cubicalDualL1 uv.1 uv.2 := by
-- proof
  apply StatMech.FrontierA.centralCylinderPairs_l1_ge_one n uv huv

/--
[centralCylinderPairs_exp_l1_sum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma centralCylinderPairs_exp_l1_sum_le_eq
  {decay : Real}
  {n : Nat}
-- given
  (hdecay : 0 < decay) :
-- imply
  (∑ uv ∈ centralCylinderPairs n, Real.exp (-decay * (cubicalDualL1 uv.1 uv.2 : Real))) <= 20 * ((1 - Real.exp (-decay))⁻¹) ^ 3 * centralSquareSide n := by
-- proof
  apply StatMech.FrontierA.centralCylinderPairs_exp_l1_sum_le decay hdecay n

/--
[exists_cubicalInfiniteVolumeWilson_perimeterLower_of_dual_lt_betaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma exists_cubicalInfiniteVolumeWilson_perimeterLower_of_dual_lt_betaC_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hlt : gaugeDualCoupling K < betaC 3) :
-- imply
  ∃ decay > 0, ∀ n, Real.exp (-(gaugePerimeterPenalty (Real.exp (-decay)) * (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) * centralSquareSide n) <= cubicalInfiniteVolumeWilsonExpectation K (centralSquareSide n) (centralSquareSide n) := by
-- proof
  apply StatMech.FrontierA.exists_cubicalInfiniteVolumeWilson_perimeterLower_of_dual_lt_betaC K hK hlt

/--
[isingBetaC_three_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma isingBetaC_three_pos_eq :
-- imply
  0 < betaC 3 := by
-- proof
  apply StatMech.FrontierA.isingBetaC_three_pos

/--
[exists_cubicalInfiniteVolumeWilson_perimeterLower_of_critical_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeInternalCylinderLimit.lean)
-/
@[path]
private lemma exists_cubicalInfiniteVolumeWilson_perimeterLower_of_critical_lt_eq
  {K : Real}
-- given
  (hK : 0 < K)
  (hhigh : gaugeCriticalCoupling (betaC 3) < K) :
-- imply
  ∃ decay > 0, ∀ n, Real.exp (-(gaugePerimeterPenalty (Real.exp (-decay)) * (20 * ((1 - Real.exp (-decay))⁻¹) ^ 3)) * centralSquareSide n) <= cubicalInfiniteVolumeWilsonExpectation K (centralSquareSide n) (centralSquareSide n) := by
-- proof
  apply StatMech.FrontierA.exists_cubicalInfiniteVolumeWilson_perimeterLower_of_critical_lt K hK hhigh


-- created on 2026-10-23
