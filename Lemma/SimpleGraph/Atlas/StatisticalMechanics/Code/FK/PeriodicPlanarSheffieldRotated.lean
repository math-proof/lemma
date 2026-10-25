import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotated
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair


/--
[matchedVerticalHorizontalCrossingEvents_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRotated.lean)
-/
@[path]
private lemma matchedVerticalHorizontalCrossingEvents_disjoint_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {B a b c d : ℝ}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B) :
-- imply
  Disjoint (D.primalEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d) ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedVerticalHorizontalCrossingEvents_disjoint D hBpos hBp hBd hab hcd

/--
[matchedVerticalHorizontalCrossing_measureReal_add_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRotated.lean)
-/
@[path]
private lemma matchedVerticalHorizontalCrossing_measureReal_add_le_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B a b c d : ℝ}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B) :
-- imply
  mu.real (D.primalEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d) + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B)) ≤ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one D mu hBpos hBp hBd hab hcd

/--
[primalCrossing_min_lt_of_dualCrossing_max_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRotated.lean)
-/
@[path]
private lemma primalCrossing_min_lt_of_dualCrossing_max_gt_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B a b c d epsilon : ℝ}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B)
  (hdual : 1 - epsilon < max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d)) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B)))) :
-- imply
  min (mu.real (D.primalEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d)) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.primalCrossing_min_lt_of_dualCrossing_max_gt D mu hBpos hBp hBd hab hcd hdual

/--
[exists_buffer_primalCrossing_min_lt_of_dualCrossing_max_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRotated.lean)
-/
@[path]
private lemma exists_buffer_primalCrossing_min_lt_of_dualCrossing_max_gt_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu] :
-- imply
  ∃ B : ℝ, 0 < B ∧ ∀ {a b c d epsilon : ℝ}, a + 5 * B < b - 5 * B → c + 5 * B < d - 5 * B → 1 - epsilon < max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d)) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B))) → min (mu.real (D.primalEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d)) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_buffer_primalCrossing_min_lt_of_dualCrossing_max_gt D mu

/--
[exists_buffer_primal_crossing_min_tendsto_zero_of_dual_max](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRotated.lean)
-/
@[path]
private lemma exists_buffer_primal_crossing_min_tendsto_zero_of_dual_max_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : ℕ → ℝ} :
-- imply
  ∃ B : ℝ, 0 < B ∧ ∀ (hspanX : ∀ n, a n + 5 * B < b n - 5 * B) (hspanY : ∀ n, c n + 5 * B < d n - 5 * B), Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a n + 4 * B) (b n - 4 * B) (c n) (d n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a n) (b n) (c n + 4 * B) (d n - 4 * B)))) atTop (nhds 1) → Tendsto (fun n => min (mu.real (D.primalEmbedding.horizontalCrossingEvent (a n) (b n) (c n + 4 * B) (d n - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a n + 4 * B) (b n - 4 * B) (c n) (d n)))) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_buffer_primal_crossing_min_tendsto_zero_of_dual_max D mu a b c d

/--
[balanced_aspect_contradiction_of_crossing_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldRotated.lean)
-/
@[path]
private lemma balanced_aspect_contradiction_of_crossing_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {a b c d dNext : Nat → Real}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
  (hspanX : ∀ n, a n + 5 * B < b n - 5 * B)
  (hspanY : ∀ n, c n + 5 * B < d n - 5 * B)
  (hspanYNext : ∀ n, c n + 5 * B < dNext n - 5 * B)
  (hbalance : ∀ n, mu.real (D.primalEmbedding.horizontalCrossingEvent (a n) (b n) (c n + 4 * B) (d n - 4 * B)) ≤ mu.real (D.primalEmbedding.verticalCrossingEvent (a n + 4 * B) (b n - 4 * B) (c n) (d n)))
  (hnext : ∀ n, mu.real (D.primalEmbedding.verticalCrossingEvent (a n + 4 * B) (b n - 4 * B) (c n) (dNext n)) ≤ mu.real (D.primalEmbedding.horizontalCrossingEvent (a n) (b n) (c n + 4 * B) (dNext n - 4 * B)))
  (hprimalMax : Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a n) (b n) (c n + 4 * B) (d n - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a n + 4 * B) (b n - 4 * B) (c n) (dNext n)))) atTop (nhds 1))
  (hdualMax : Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a n + 4 * B) (b n - 4 * B) (c n) (d n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a n) (b n) (c n + 4 * B) (d n - 4 * B)))) atTop (nhds 1))
  (hdualMaxNext : Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a n + 4 * B) (b n - 4 * B) (c n) (dNext n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a n) (b n) (c n + 4 * B) (dNext n - 4 * B)))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.balanced_aspect_contradiction_of_crossing_limits D mu hBpos hBp hBd a b c d dNext hspanX hspanY hspanYNext hbalance hnext hprimalMax hdualMax hdualMaxNext


-- created on 2026-10-23
