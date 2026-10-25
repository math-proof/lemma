import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldSynchronization
open Filter MeasureTheory Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[adjacent_height_array_contradiction_of_endpoint_and_uniform_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldSynchronization.lean)
-/
@[path]
private lemma adjacent_height_array_contradiction_of_endpoint_and_uniform_limits_eq
-- given
  (horizontal vertical : Nat -> Nat -> Real)
  (K : Nat -> Nat)
  (hhorizontal_nonneg : forall n k, 0 <= horizontal n k)
  (hvertical_nonneg : forall n k, 0 <= vertical n k)
  (hhorizontal_le_one : forall n k, horizontal n k <= 1)
  (hvertical_le_one : forall n k, vertical n k <= 1)
  (hvertical_start : Tendsto (fun n => vertical n 0) atTop (nhds 1))
  (hhorizontal_end : Tendsto (fun n => horizontal n (K n + 1)) atTop (nhds 1))
  (hlimits : forall k : Nat -> Nat, (forall n, k n < K n + 1) -> Tendsto (fun n => max (horizontal n (k n)) (vertical n (k n + 1))) atTop (nhds 1) /\ Tendsto (fun n => min (vertical n (k n)) (horizontal n (k n))) atTop (nhds 0) /\ Tendsto (fun n => min (vertical n (k n + 1)) (horizontal n (k n + 1))) atTop (nhds 0)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.adjacent_height_array_contradiction_of_endpoint_and_uniform_limits horizontal vertical K hhorizontal_nonneg hvertical_nonneg hhorizontal_le_one hvertical_le_one hvertical_start hhorizontal_end hlimits

/--
[branchAlignedComplementaryLimits_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldSynchronization.lean)
-/
@[path]
private lemma branchAlignedComplementaryLimits_false_eq
-- given
  (branch : Nat -> Bool)
  (H V dualV dualH : Nat -> Real)
  (hHdual : forall n, H n + dualV n <= 1)
  (hVdual : forall n, V n + dualH n <= 1)
  (hprimal : Tendsto (fun n => if branch n then V n else H n) atTop (nhds 1))
  (hdual : Tendsto (fun n => if branch n then dualH n else dualV n) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.branchAlignedComplementaryLimits_false branch H V dualV dualH hHdual hVdual hprimal hdual

/--
[balancedAdjacentSelectorsComplementary_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldSynchronization.lean)
-/
@[path]
private lemma balancedAdjacentSelectorsComplementary_false_eq
-- given
  (H0 V0 H1 V1 dualV0 dualH0 dualV1 dualH1 error : Nat -> Real)
  (hH0_nonneg : forall n, 0 <= H0 n)
  (hV0_nonneg : forall n, 0 <= V0 n)
  (hH1_nonneg : forall n, 0 <= H1 n)
  (hV1_nonneg : forall n, 0 <= V1 n)
  (hH0_le_one : forall n, H0 n <= 1)
  (hV0_le_one : forall n, V0 n <= 1)
  (hH1_le_one : forall n, H1 n <= 1)
  (hV1_le_one : forall n, V1 n <= 1)
  (hbalance : forall n, H0 n <= V0 n + error n)
  (hnext : forall n, V1 n <= H1 n + error n)
  (herror : Tendsto error atTop (nhds 0))
  (hadjacent : Tendsto (fun n => max (H0 n) (V1 n)) atTop (nhds 1))
  (hdual0 : Tendsto (fun n => max (dualV0 n) (dualH0 n)) atTop (nhds 1))
  (hdual1 : Tendsto (fun n => max (dualV1 n) (dualH1 n)) atTop (nhds 1))
  (hmatchH0 : forall n, H0 n + dualV0 n <= 1)
  (hmatchV0 : forall n, V0 n + dualH0 n <= 1)
  (hmatchH1 : forall n, H1 n + dualV1 n <= 1)
  (hmatchV1 : forall n, V1 n + dualH1 n <= 1) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.balancedAdjacentSelectorsComplementary_false H0 V0 H1 V1 dualV0 dualH0 dualV1 dualH1 error hH0_nonneg hV0_nonneg hH1_nonneg hV1_nonneg hH0_le_one hV0_le_one hH1_le_one hV1_le_one hbalance hnext herror hadjacent hdual0 hdual1 hmatchH0 hmatchV0 hmatchH1 hmatchV1

/--
[adjacent_height_array_contradiction_of_primal_dual_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldSynchronization.lean)
-/
@[path]
private lemma adjacent_height_array_contradiction_of_primal_dual_limits_eq
-- given
  (horizontal vertical dualVertical dualHorizontal : Nat -> Nat -> Real)
  (K : Nat -> Nat)
  (hhorizontal_nonneg : forall n k, 0 <= horizontal n k)
  (hvertical_nonneg : forall n k, 0 <= vertical n k)
  (hhorizontal_le_one : forall n k, horizontal n k <= 1)
  (hvertical_le_one : forall n k, vertical n k <= 1)
  (hvertical_start : Tendsto (fun n => vertical n 0) atTop (nhds 1))
  (hhorizontal_end : Tendsto (fun n => horizontal n (K n + 1)) atTop (nhds 1))
  (hmatchHorizontal : forall n k, horizontal n k + dualVertical n k <= 1)
  (hmatchVertical : forall n k, vertical n k + dualHorizontal n k <= 1)
  (hprimalLimits : forall k : Nat -> Nat, (forall n, k n < K n + 1) -> Tendsto (fun n => max (horizontal n (k n)) (vertical n (k n + 1))) atTop (nhds 1))
  (hdualLimits : forall k : Nat -> Nat, Tendsto (fun n => max (dualVertical n (k n)) (dualHorizontal n (k n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.adjacent_height_array_contradiction_of_primal_dual_limits horizontal vertical dualVertical dualHorizontal K hhorizontal_nonneg hvertical_nonneg hhorizontal_le_one hvertical_le_one hvertical_start hhorizontal_end hmatchHorizontal hmatchVertical hprimalLimits hdualLimits

/--
[PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_max_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldSynchronization.lean)
-/
@[path]
private lemma adjacent_rectangles_contradiction_of_max_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
  (a b c d : Nat -> Nat -> Real)
  (K : Nat -> Nat)
  (hspanX : ∀ n k, a n k + 5 * B < b n k - 5 * B)
  (hspanY : ∀ n k, c n k + 5 * B < d n k - 5 * B)
  (hvertical_start : Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (a n 0 + 4 * B) (b n 0 - 4 * B) (c n 0) (d n 0))) atTop (nhds 1))
  (hhorizontal_end : Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (a n (K n + 1)) (b n (K n + 1)) (c n (K n + 1) + 4 * B) (d n (K n + 1) - 4 * B))) atTop (nhds 1))
  (hprimalLimits : ∀ k : Nat -> Nat, (∀ n, k n < K n + 1) -> Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a n (k n)) (b n (k n)) (c n (k n) + 4 * B) (d n (k n) - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a n (k n + 1) + 4 * B) (b n (k n + 1) - 4 * B) (c n (k n + 1)) (d n (k n + 1))))) atTop (nhds 1))
  (hdualLimits : ∀ k : Nat -> Nat, Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a n (k n) + 4 * B) (b n (k n) - 4 * B) (c n (k n)) (d n (k n)))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a n (k n)) (b n (k n)) (c n (k n) + 4 * B) (d n (k n) - 4 * B)))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.adjacent_rectangles_contradiction_of_max_limits D mu hBpos hBp hBd a b c d K hspanX hspanY hvertical_start hhorizontal_end hprimalLimits hdualLimits


-- created on 2026-10-23
