import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.verticalCrossingEvent_mono_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldVariablePadding.lean)
-/
@[path]
private lemma verticalCrossingEvent_mono_horizontal_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a' a b b' c d : Real}
-- given
  (ha : a' ≤ a)
  (hb : b ≤ b') :
-- imply
  E.verticalCrossingEvent a b c d ⊆ E.verticalCrossingEvent a' b' c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossingEvent_mono_horizontal E ha hb

/--
[PeriodicPlaneEmbedding.horizontalCrossingEvent_mono_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldVariablePadding.lean)
-/
@[path]
private lemma horizontalCrossingEvent_mono_vertical_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {a b c' c d d' : Real}
-- given
  (hc : c' ≤ c)
  (hd : d ≤ d') :
-- imply
  E.horizontalCrossingEvent a b c d ⊆ E.horizontalCrossingEvent a b c' d' := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossingEvent_mono_vertical E hc hd

/--
[PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_mono_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldVariablePadding.lean)
-/
@[path]
private lemma verticalCrossing_tendsto_one_mono_horizontal_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (a b c d a' b' : Nat -> Real)
  (ha : forall n, a' n <= a n)
  (hb : forall n, b n <= b' n)
  (hlimit : Tendsto (fun n => mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => mu.real (E.verticalCrossingEvent (a' n) (b' n) (c n) (d n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_tendsto_one_mono_horizontal E mu a b c d a' b' ha hb hlimit

/--
[PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_mono_vertical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldVariablePadding.lean)
-/
@[path]
private lemma horizontalCrossing_tendsto_one_mono_vertical_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (a b c d c' d' : Nat -> Real)
  (hc : forall n, c' n <= c n)
  (hd : forall n, d n <= d' n)
  (hlimit : Tendsto (fun n => mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => mu.real (E.horizontalCrossingEvent (a n) (b n) (c' n) (d' n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_mono_vertical E mu a b c d c' d' hc hd hlimit

/--
[PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_pads](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldVariablePadding.lean)
-/
@[path]
private lemma matchedCrossing_measureReal_add_le_one_of_pads_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B xPad yPad a b c d : Real}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
  (hxPad : 4 * B ≤ xPad)
  (hyPad : 4 * B ≤ yPad)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B) :
-- imply
  mu.real (D.primalEmbedding.horizontalCrossingEvent a b (c + yPad) (d - yPad)) + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a + xPad) (b - xPad) c d) ≤ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_pads D mu hBpos hBp hBd hxPad hyPad hab hcd

/--
[PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldVariablePadding.lean)
-/
@[path]
private lemma matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B xPad yPad a b c d : Real}
-- given
  (hBpos : 0 < B)
  (hBp : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| ≤ B)
  (hBd : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| ≤ B)
  (hxPad : 4 * B ≤ xPad)
  (hyPad : 4 * B ≤ yPad)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B) :
-- imply
  mu.real (D.primalEmbedding.verticalCrossingEvent (a + xPad) (b - xPad) c d) + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent a b (c + yPad) (d - yPad)) ≤ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_pads D mu hBpos hBp hBd hxPad hyPad hab hcd

/--
[PeriodicPlanarDualPair.VariablePadTwoLevelRectangleArray.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldVariablePadding.lean)
-/
@[path]
private lemma false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {data : D.VariablePadTwoLevelRectangleArray mu B} :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.VariablePadTwoLevelRectangleArray.false D mu data


-- created on 2026-10-23
