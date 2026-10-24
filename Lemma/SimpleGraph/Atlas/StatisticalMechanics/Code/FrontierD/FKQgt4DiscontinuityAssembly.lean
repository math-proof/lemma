import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4DiscontinuityAssembly
open MeasureTheory Filter Topology StatMech StatMech.FrontierD


/--
[fkQgt4CriticalFreeDiagonalTwoPoint_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiscontinuityAssembly.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeDiagonalTwoPoint_nonneg_eq
  {q : Real}
  {n : Nat}
-- given
  (hq : 4 < q) :
-- imply
  0 <= fkQgt4CriticalFreeDiagonalTwoPoint hq n := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeDiagonalTwoPoint_nonneg hq n

/--
[fkQgt4CriticalFreeDiagonalTwoPoint_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiscontinuityAssembly.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeDiagonalTwoPoint_le_one_eq
  {q : Real}
  {n : Nat}
-- given
  (hq : 4 < q) :
-- imply
  fkQgt4CriticalFreeDiagonalTwoPoint hq n <= 1 := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeDiagonalTwoPoint_le_one hq n

/--
[tendsto_zero_of_neg_log_div_tendsto_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiscontinuityAssembly.lean)
-/
@[path]
private lemma tendsto_zero_of_neg_log_div_tendsto_pos_eq
  {xi : Real}
-- given
  (f : Nat -> Real)
  (hf0 : forall n, 0 <= f n)
  (hxi : 0 < xi)
  (hrate : Tendsto (fun n => -Real.log (f n) / (n + 1 : Real)) atTop (nhds xi)) :
-- imply
  Tendsto f atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_zero_of_neg_log_div_tendsto_pos f hf0 hxi hrate

/--
[fkQgt4CriticalFreeDiagonalTwoPoint_tendsto_zero_of_rate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiscontinuityAssembly.lean)
-/
@[path]
private lemma fkQgt4CriticalFreeDiagonalTwoPoint_tendsto_zero_of_rate_eq
  {q xi : Real}
-- given
  (hq : 4 < q)
  (hxi : 0 < xi)
  (hrate : Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds xi)) :
-- imply
  Tendsto (fun n => fkQgt4CriticalFreeDiagonalTwoPoint hq (n + 1)) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.fkQgt4CriticalFreeDiagonalTwoPoint_tendsto_zero_of_rate hq hxi hrate

/--
[percolationProbability_eq_zero_of_twoPoint_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiscontinuityAssembly.lean)
-/
@[path]
private lemma percolationProbability_eq_zero_of_twoPoint_tendsto_zero_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsFiniteMeasure mu]
-- given
  (hPA : forall x : Site d, mu.real (FK.clusterInfiniteEvent d (origin d)) * mu.real (FK.clusterInfiniteEvent d x) <= mu.real (FK.clusterInfiniteEvent d (origin d) ∩ FK.clusterInfiniteEvent d x))
  (hTI : forall x : Site d, mu.real (FK.clusterInfiniteEvent d x) = mu.real (FK.clusterInfiniteEvent d (origin d)))
  (huniq : mu (atLeastTwoInfinite d) = 0)
  (x : Nat -> Site d)
  (hdecay : Tendsto (fun n => FK.infiniteTwoPointReal mu (origin d) (x n)) atTop (nhds 0)) :
-- imply
  mu.real (percolationEvent d) = 0 := by
-- proof
  apply StatMech.FrontierD.percolationProbability_eq_zero_of_twoPoint_tendsto_zero mu hPA hTI huniq x hdecay

/--
[clusterInfiniteEvent_real_eq_origin_of_translationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiscontinuityAssembly.lean)
-/
@[path]
private lemma clusterInfiniteEvent_real_eq_origin_of_translationInvariant_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  {x : Site d}
-- given
  (htrans : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site d)) mu) :
-- imply
  mu.real (FK.clusterInfiniteEvent d x) = mu.real (FK.clusterInfiniteEvent d (origin d)) := by
-- proof
  apply StatMech.FrontierD.clusterInfiniteEvent_real_eq_origin_of_translationInvariant mu htrans x

/--
[oneInfiniteCluster_ae_of_theta_pos_of_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiscontinuityAssembly.lean)
-/
@[path]
private lemma oneInfiniteCluster_ae_of_theta_pos_of_zero_one_eq
  {d : Nat}
  {mu : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure mu]
-- given
  (htheta : 0 < mu.real (percolationEvent d))
  (hzeroOne : mu {omega | numInfiniteClusters d omega = 0} = 1 ∨ mu {omega | numInfiniteClusters d omega = 1} = 1) :
-- imply
  mu {omega | numInfiniteClusters d omega = 1} = 1 := by
-- proof
  apply StatMech.FrontierD.oneInfiniteCluster_ae_of_theta_pos_of_zero_one mu htheta hzeroOne

/--
[FKQgt4TorusSixVertexWindingBridge.toBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiscontinuityAssembly.lean)
-/
@[path]
private lemma toBounds_eq
  {xiInv R : Real}
-- given
  (h : FKQgt4TorusSixVertexWindingBridge xiInv R) :
-- imply
  FKQgt4WindingSectorBounds xiInv R := by
-- proof
  apply StatMech.FrontierD.FKQgt4TorusSixVertexWindingBridge.toBounds h

/--
[fkQgt4_discontinuity_of_winding_and_order_inputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4DiscontinuityAssembly.lean)
-/
@[path]
private lemma fkQgt4_discontinuity_of_winding_and_order_inputs_eq
  {q xiInv : Real}
-- given
  (hq : 4 < q)
  (hxi : 0 < xiInv)
  (hrate : Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds xiInv))
  (hWiredAlmostSure : let mu := ((FK.wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2))) ) mu (percolationEvent 2) = 1)
  (hwind : FKQgt4TorusSixVertexWindingBridge xiInv (fkQgt4SixVertexGapRate q)) :
-- imply
  FK.IsFirstOrderTransition 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) ∧ FK.freeInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) ≠ FK.wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) ∧ Tendsto (fkQgt4CriticalFreeDiagonalRate hq) atTop (nhds (fkQgt4SixVertexGapRate q)) ∧ 0 < fkQgt4SixVertexGapRate q ∧ (((FK.wiredInfiniteVolume 2 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).1 (BeffaraDC.selfDualPoint_mem_Ioo (by linarith : (0 : Real) < q)).2 (by linarith : (0 : Real) < q) : ProbabilityMeasure (ConfigSpace (Sym2 (Site 2)))) : Measure (ConfigSpace (Sym2 (Site 2)))) (percolationEvent 2) = 1) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_discontinuity_of_winding_and_order_inputs hq hxi hrate hWiredAlmostSure hwind


-- created on 2026-10-23
