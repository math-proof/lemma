import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part9
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[exists_carriedAsymmetricEndpointCoordinates_with_radius_requirements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_carriedAsymmetricEndpointCoordinates_with_radius_requirements_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {B : Nat}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hBpos : 0 < B)
  (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z) (u) (i : Fin 2), |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
  (template : Nat -> Finset V)
  (minimumWidth targetY : Nat -> Nat -> Nat)
  (hminimumWidth : forall n radius, 3 * B + 1 <= minimumWidth n radius)
  (htargetY : forall n radius, 20 * B + 1 <= targetY n radius) :
-- imply
  exists radius width height : Nat -> Nat, Tendsto radius atTop atTop /\ (forall n, minimumWidth n (radius n) <= width n) /\ (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template (n + 1)) ((template (n + 1)).image (P.shift (preferenceKingOffset (q (n + 1)).2 + if (q (n + 1)).1.val = 0 then 0 else verticalShift (height n)))) (radius (n + 1)))) atTop (nhds 0)) /\ Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent (4 * B) (4 * B + width n) (-4 * B) (targetY n (radius n) + 4 * B))) atTop (nhds 1) /\ Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent (-4 * B) (width n + 12 * B) (4 * B) (4 * B + height n))) atTop (nhds 1) /\ (forall n, (0 : Real) + 5 * B < width n + 8 * B - 5 * B) /\ (forall n, -(4 * B : Real) + 5 * B < targetY n (radius n) + 4 * B - 5 * B) /\ (forall n, -(4 * B : Real) + 5 * B < width n + 12 * B - 5 * B) /\ (forall n, (0 : Real) + 5 * B < targetY n (radius n) + height n - 5 * B) /\ (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\ (forall n, (4 * B : Real) + width n <= width n + 8 * B - 4 * B) /\ (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\ (forall n, (4 * B : Real) + height n <= targetY n (radius n) + height n - 4 * B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_carriedAsymmetricEndpointCoordinates_with_radius_requirements E Edual mu muDual hunique hFKGDual hTIDual huniqueDual B hBpos hB template minimumWidth targetY hminimumWidth htargetY

/--
[exists_carriedAsymmetricEndpointCoordinates_with_requirements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_carriedAsymmetricEndpointCoordinates_with_requirements_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {B : Nat}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hBpos : 0 < B)
  (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z) (u) (i : Fin 2), |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
  (template : Nat -> Finset V)
  (minimumWidth targetY : Nat -> Nat)
  (hminimumWidth : forall n, 3 * B + 1 <= minimumWidth n)
  (htargetY : forall n, 20 * B + 1 <= targetY n) :
-- imply
  exists radius width height : Nat -> Nat, Tendsto radius atTop atTop /\ (forall n, minimumWidth n <= width n) /\ (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template (n + 1)) ((template (n + 1)).image (P.shift (preferenceKingOffset (q (n + 1)).2 + if (q (n + 1)).1.val = 0 then 0 else verticalShift (height n)))) (radius (n + 1)))) atTop (nhds 0)) /\ Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent (4 * B) (4 * B + width n) (-4 * B) (targetY n + 4 * B))) atTop (nhds 1) /\ Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent (-4 * B) (width n + 12 * B) (4 * B) (4 * B + height n))) atTop (nhds 1) /\ (forall n, (0 : Real) + 5 * B < width n + 8 * B - 5 * B) /\ (forall n, -(4 * B : Real) + 5 * B < targetY n + 4 * B - 5 * B) /\ (forall n, -(4 * B : Real) + 5 * B < width n + 12 * B - 5 * B) /\ (forall n, (0 : Real) + 5 * B < targetY n + height n - 5 * B) /\ (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\ (forall n, (4 * B : Real) + width n <= width n + 8 * B - 4 * B) /\ (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\ (forall n, (4 * B : Real) + height n <= targetY n + height n - 4 * B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_carriedAsymmetricEndpointCoordinates_with_requirements E Edual mu muDual hunique hFKGDual hTIDual huniqueDual B hBpos hB template minimumWidth targetY hminimumWidth htargetY

/--
[PeriodicPlanarDualPair.exists_carriedAsymmetricEndpoints_false_of_primal_limit_with_requirements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_carriedAsymmetricEndpoints_false_of_primal_limit_with_requirements_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Nat}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG (D.dualMeasure mu))
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
  (huniqueDual : (D.dualMeasure mu) {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hBpos : 0 < B)
  (hBp : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxz u - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x z : W} (hxz : Pdual.graph.Adj x z) (u) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxz u - D.dualEmbedding.vertex x) i| <= B)
  (template : Nat -> Finset V)
  (minimumWidth targetY : Nat -> Nat)
  (hminimumWidth : forall n, 3 * B + 1 <= minimumWidth n)
  (htargetY : forall n, 20 * B + 1 <= targetY n) :
-- imply
  exists radius width height : Nat -> Nat, Tendsto radius atTop atTop /\ (forall n, minimumWidth n <= width n) /\ (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template (n + 1)) ((template (n + 1)).image (P.shift (preferenceKingOffset (q (n + 1)).2 + if (q (n + 1)).1.val = 0 then 0 else verticalShift (height n)))) (radius (n + 1)))) atTop (nhds 0)) /\ (Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent 0 (width n + 8 * B) 0 (targetY n))) (mu.real (D.primalEmbedding.verticalCrossingEvent 0 (width n + 8 * B) 0 (targetY n + height n)))) atTop (nhds 1) -> False) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_carriedAsymmetricEndpoints_false_of_primal_limit_with_requirements D mu hunique hFKGDual hTIDual huniqueDual B hBpos hBp hBd template minimumWidth targetY hminimumWidth htargetY

/--
[PeriodicPlaneEmbedding.centeredCrossingMax_tendsto_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma centeredCrossingMax_tendsto_origin_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hTI : P.IsTranslationInvariant mu)
  (M outerWidth outerHeight step : Nat -> Nat)
  (hwidth : forall n, 2 * M n <= outerWidth n)
  (hheight : forall n, 2 * M n <= outerHeight n)
  (hcentered : Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (-(M n : Real)) (M n + (outerWidth n - 2 * M n) : Nat) (-(M n : Real)) (M n + (outerHeight n - 2 * M n) : Nat))) (mu.real (E.verticalCrossingEvent (-(M n : Real)) (M n + (outerWidth n - 2 * M n) : Nat) (-(M n : Real)) ((M n + (outerHeight n - 2 * M n) : Nat) + step n)))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent 0 (outerWidth n) 0 (outerHeight n))) (mu.real (E.verticalCrossingEvent 0 (outerWidth n) 0 (outerHeight n + step n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.centeredCrossingMax_tendsto_origin E mu hTI M outerWidth outerHeight step hwidth hheight hcentered

/--
[PeriodicPlaneEmbedding.adjacentCrossingMax_tendsto_one_mono_vertical_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma adjacentCrossingMax_tendsto_one_mono_vertical_width_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (a b c d step aVertical bVertical : Nat -> Real)
  (ha : forall n, aVertical n <= a n)
  (hb : forall n, b n <= bVertical n)
  (hlimit : Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n + step n)))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.verticalCrossingEvent (aVertical n) (bVertical n) (c n) (d n + step n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.adjacentCrossingMax_tendsto_one_mono_vertical_width E mu a b c d step aVertical bVertical ha hb hlimit

/--
[PeriodicPlanarDualPair.pointwiseRecursiveRectangleArray_false_of_primal_dualMeasure_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma pointwiseRecursiveRectangleArray_false_of_primal_dualMeasure_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a b c d : Nat -> Nat -> Real)
  (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
  (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
  (hverticalStart : Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (a 0 n + 4 * B) (b 0 n - 4 * B) (c 0 n) (d 0 n))) atTop (nhds 1))
  (hhorizontalLevel : forall k, Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (a (k + 1) n) (b (k + 1) n) (c (k + 1) n + 4 * B) (d (k + 1) n - 4 * B))) atTop (nhds 1))
  (hnormalAdjacent : forall k, Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a (k + 1) n + 4 * B) (b (k + 1) n - 4 * B) (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
  (hdualLevel : forall k, Tendsto (fun n => max ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent (a k n + 4 * B) (b k n - 4 * B) (c k n) (d k n))) ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B)))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.pointwiseRecursiveRectangleArray_false_of_primal_dualMeasure_limits D mu B hBpos hBp hBd a b c d hspanX hspanY hverticalStart hhorizontalLevel hnormalAdjacent hdualLevel

/--
[PeriodicPlanarDualPair.EndpointBridgedRectangleArrayCertificate.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : D.EndpointBridgedRectangleArrayCertificate mu} :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.EndpointBridgedRectangleArrayCertificate.false D mu data

/--
[PeriodicPlaneEmbedding.verticalEndpoint_tendsto_startBridge_of_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma verticalEndpoint_tendsto_startBridge_of_mono_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (startA startB startC startD lowerA lowerB : Nat -> Real)
  (hlowerA : forall n, lowerA n <= startA n)
  (hlowerB : forall n, startB n <= lowerB n)
  (hvertical : Tendsto (fun n => mu.real (E.verticalCrossingEvent (startA n + 4 * B) (startB n - 4 * B) (startC n) (startD n))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (startA n) (startB n) (startC n + 4 * B) (startD n - 4 * B))) (mu.real (E.verticalCrossingEvent (lowerA n + 4 * B) (lowerB n - 4 * B) (startC n) (startD n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalEndpoint_tendsto_startBridge_of_mono E mu B startA startB startC startD lowerA lowerB hlowerA hlowerB hvertical

/--
[PeriodicPlaneEmbedding.horizontalEndpoint_tendsto_endBridge_of_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma horizontalEndpoint_tendsto_endBridge_of_mono_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (endA endB upperC upperD endC endD : Nat -> Real)
  (hupperC : forall n, upperC n <= endC n)
  (hupperD : forall n, endD n <= upperD n)
  (hhorizontal : Tendsto (fun n => mu.real (E.horizontalCrossingEvent (endA n) (endB n) (endC n + 4 * B) (endD n - 4 * B))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (endA n) (endB n) (upperC n + 4 * B) (upperD n - 4 * B))) (mu.real (E.verticalCrossingEvent (endA n + 4 * B) (endB n - 4 * B) (endC n) (endD n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalEndpoint_tendsto_endBridge_of_mono E mu B endA endB upperC upperD endC endD hupperC hupperD hhorizontal

/--
[PeriodicGraph.exists_finiteAdjacentHeights_pairMergeRadius_at_error](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_finiteAdjacentHeights_pairMergeRadius_at_error_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Finset V}
  {steps : Finset Int}
  {cutoff : Nat}
  {epsilon : Real}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  exists radius : Nat, cutoff <= radius /\ forall step, step ∈ steps -> forall q : Fin 2 × (Fin 3 × Fin 3), mu.real (P.pairMergeErrorUnion template (template.image (P.shift (preferenceKingOffset q.2 + if q.1.val = 0 then 0 else verticalShift step))) radius) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.exists_finiteAdjacentHeights_pairMergeRadius_at_error P mu hunique template steps cutoff hepsilon

/--
[PeriodicPlaneEmbedding.exists_finiteWidth_horizontalEndpointHeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_finiteWidth_horizontalEndpointHeight_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {widths : Finset Nat}
  {y : Real}
  {minimumHeight : Nat}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (horizontalLeft horizontalRight : Nat -> Int)
  (hspan : forall width, width ∈ widths -> 3 * B < horizontalRight width - horizontalLeft width)
  (hepsilon : 0 < epsilon) :
-- imply
  exists height : Nat, minimumHeight <= height /\ forall width, width ∈ widths -> 1 - epsilon < mu.real (E.horizontalCrossingEvent (horizontalLeft width) (horizontalRight width) y (y + height)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_finiteWidth_horizontalEndpointHeight E mu hFKG hTI hunique B hB0 hB widths horizontalLeft horizontalRight y minimumHeight hspan hepsilon

/--
[PeriodicPlaneEmbedding.exists_finiteHeight_verticalEndpointWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_finiteHeight_verticalEndpointWidth_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {x : Real}
  {minimumWidth : Nat}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (heights : Finset Nat)
  (verticalBottom verticalTop : Nat -> Int)
  (hspan : forall height, height ∈ heights -> 3 * B < verticalTop height - verticalBottom height)
  (hepsilon : 0 < epsilon) :
-- imply
  exists width : Nat, minimumWidth <= width /\ forall height, height ∈ heights -> 1 - epsilon < mu.real (E.verticalCrossingEvent x (x + width) (verticalBottom height) (verticalTop height)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_finiteHeight_verticalEndpointWidth E mu hFKG hTI hunique B hB0 hB heights verticalBottom verticalTop x minimumWidth hspan hepsilon

/--
[PeriodicPlaneEmbedding.exists_finiteHeight_coupledEndpointWidthHeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_finiteHeight_coupledEndpointWidthHeight_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {x y : Real}
  {minimumWidth minimumHeight : Nat}
  {verticalEpsilon horizontalEpsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (heights : Finset Nat)
  (verticalBottom verticalTop : Nat -> Int)
  (horizontalLeft horizontalRight : Nat -> Int)
  (hverticalSpan : forall step, step ∈ heights -> 3 * B < verticalTop step - verticalBottom step)
  (hhorizontalSpan : forall width, minimumWidth <= width -> 3 * B < horizontalRight width - horizontalLeft width)
  (hVerticalEpsilon : 0 < verticalEpsilon)
  (hHorizontalEpsilon : 0 < horizontalEpsilon) :
-- imply
  exists width height : Nat, minimumWidth <= width /\ minimumHeight <= height /\ (forall step, step ∈ heights -> 1 - verticalEpsilon < mu.real (E.verticalCrossingEvent x (x + width) (verticalBottom step) (verticalTop step))) /\ 1 - horizontalEpsilon < mu.real (E.horizontalCrossingEvent (horizontalLeft width) (horizontalRight width) y (y + height)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_finiteHeight_coupledEndpointWidthHeight E mu hFKG hTI hunique B hB0 hB heights verticalBottom verticalTop x y minimumWidth minimumHeight horizontalLeft horizontalRight hverticalSpan hhorizontalSpan hVerticalEpsilon hHorizontalEpsilon

/--
[PeriodicPlaneEmbedding.exists_finiteWidth_endpointHeight_pairMergeRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_finiteWidth_endpointHeight_pairMergeRadius_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {template : Finset V}
  {widths : Finset Nat}
  {y : Real}
  {minimumHeight cutoff : Nat}
  {endpointEpsilon mergeEpsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (horizontalLeft horizontalRight : Nat -> Int)
  (hspan : forall width, width ∈ widths -> 3 * B < horizontalRight width - horizontalLeft width)
  (hEndpointEpsilon : 0 < endpointEpsilon)
  (hMergeEpsilon : 0 < mergeEpsilon) :
-- imply
  exists height radius : Nat, minimumHeight <= height /\ cutoff <= radius /\ (forall width, width ∈ widths -> 1 - endpointEpsilon < mu.real (E.horizontalCrossingEvent (horizontalLeft width) (horizontalRight width) y (y + height))) /\ forall step : Nat, step <= height -> forall q : Fin 2 × (Fin 3 × Fin 3), mu.real (P.pairMergeErrorUnion template (template.image (P.shift (preferenceKingOffset q.2 + if q.1.val = 0 then 0 else verticalShift step))) radius) < mergeEpsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_finiteWidth_endpointHeight_pairMergeRadius E mu hFKG hTI hunique B hB0 hB template widths horizontalLeft horizontalRight y minimumHeight cutoff hspan hEndpointEpsilon hMergeEpsilon

/--
[PeriodicPlaneEmbedding.nonempty_finiteWidthEndpointMergeRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma nonempty_finiteWidthEndpointMergeRow_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {template : Finset V}
  {widths : Finset Nat}
  {y : Real}
  {minimumHeight cutoff : Nat}
  {endpointEpsilon mergeEpsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (horizontalLeft horizontalRight : Nat -> Int)
  (hspan : forall width, width ∈ widths -> 3 * B < horizontalRight width - horizontalLeft width)
  (hEndpointEpsilon : 0 < endpointEpsilon)
  (hMergeEpsilon : 0 < mergeEpsilon) :
-- imply
  Nonempty (E.FiniteWidthEndpointMergeRow mu template widths horizontalLeft horizontalRight y minimumHeight cutoff endpointEpsilon mergeEpsilon) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.nonempty_finiteWidthEndpointMergeRow E mu hFKG hTI hunique B hB0 hB template widths horizontalLeft horizontalRight y minimumHeight cutoff hspan hEndpointEpsilon hMergeEpsilon

/--
[PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.nonempty_verticalEndpointExtension](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma nonempty_verticalEndpointExtension_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {template : Finset V}
  {widths : Finset Nat}
  {y : Real}
  {minimumHeight cutoff : Nat}
  {endpointEpsilon mergeEpsilon : Real}
  {row : E.FiniteWidthEndpointMergeRow mu template widths horizontalLeft horizontalRight y minimumHeight cutoff endpointEpsilon mergeEpsilon}
  {x : Real}
  {minimumWidth : Nat}
  {verticalEndpointEpsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (horizontalLeft horizontalRight : Nat -> Int)
  (verticalBottom verticalTop : Nat -> Int)
  (hspan : forall step : Nat, step <= row.height -> 3 * B < verticalTop step - verticalBottom step)
  (hVerticalEndpointEpsilon : 0 < verticalEndpointEpsilon) :
-- imply
  Nonempty (row.VerticalEndpointExtension verticalBottom verticalTop x minimumWidth verticalEndpointEpsilon) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.nonempty_verticalEndpointExtension E mu hFKG hTI hunique B hB0 hB template widths horizontalLeft horizontalRight y minimumHeight cutoff endpointEpsilon mergeEpsilon row verticalBottom verticalTop x minimumWidth verticalEndpointEpsilon hspan hVerticalEndpointEpsilon

/--
[PeriodicPlaneEmbedding.exists_recursiveFiniteWidthEndpointMergeRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_recursiveFiniteWidthEndpointMergeRows_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {initialWidths : Finset Nat}
  {y : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (template : Nat -> Finset V)
  (horizontalLeft horizontalRight : Nat -> Int)
  (minimumHeight cutoff : Nat -> Nat)
  (endpointEpsilon mergeEpsilon : Nat -> Real)
  (hspan : forall width, 3 * B < horizontalRight width - horizontalLeft width)
  (hEndpointEpsilon : forall n, 0 < endpointEpsilon n)
  (hMergeEpsilon : forall n, 0 < mergeEpsilon n) :
-- imply
  exists widths : Nat -> Finset Nat, exists rows : forall n, E.FiniteWidthEndpointMergeRow mu (template n) (widths n) horizontalLeft horizontalRight y (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n), widths 0 = initialWidths /\ (forall n, widths n ⊆ widths (n + 1)) /\ forall n, E.connectorMarginRequirement (rows n).radius ∈ widths (n + 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_recursiveFiniteWidthEndpointMergeRows E mu hFKG hTI hunique B hB0 hB template initialWidths horizontalLeft horizontalRight y minimumHeight cutoff endpointEpsilon mergeEpsilon hspan hEndpointEpsilon hMergeEpsilon

/--
[PeriodicPlaneEmbedding.exists_recursiveMonotoneFiniteWidthEndpointMergeRows](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_recursiveMonotoneFiniteWidthEndpointMergeRows_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {initialWidths : Finset Nat}
  {y : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (template : Nat -> Finset V)
  (horizontalLeft horizontalRight : Nat -> Int)
  (minimumHeight cutoff : Nat -> Nat)
  (endpointEpsilon mergeEpsilon : Nat -> Real)
  (hspan : forall width, 3 * B < horizontalRight width - horizontalLeft width)
  (hEndpointEpsilon : forall n, 0 < endpointEpsilon n)
  (hMergeEpsilon : forall n, 0 < mergeEpsilon n) :
-- imply
  exists state : Nat -> Finset Nat × Nat, exists rows : forall n, E.FiniteWidthEndpointMergeRow mu (template n) (state n).1 horizontalLeft horizontalRight y (max (minimumHeight n) (state n).2) (cutoff n) (endpointEpsilon n) (mergeEpsilon n), state 0 = (initialWidths, 0) /\ (forall n, state (n + 1) = (insert (E.connectorMarginRequirement (rows n).radius) (state n).1, (rows n).height)) /\ (forall n, (state n).1 ⊆ (state (n + 1)).1) /\ (forall n, E.connectorMarginRequirement (rows n).radius ∈ (state (n + 1)).1) /\ forall n, (rows n).height <= (rows (n + 1)).height := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_recursiveMonotoneFiniteWidthEndpointMergeRows E mu hFKG hTI hunique B hB0 hB template initialWidths horizontalLeft horizontalRight y minimumHeight cutoff endpointEpsilon mergeEpsilon hspan hEndpointEpsilon hMergeEpsilon

/--
[PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.horizontalEndpoint_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma horizontalEndpoint_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {y : Real}
  {rows : forall n, E.FiniteWidthEndpointMergeRow mu (template n) (widths n) horizontalLeft horizontalRight y (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n)}
-- given
  (template : Nat -> Finset V)
  (widths : Nat -> Finset Nat)
  (horizontalLeft horizontalRight : Nat -> Int)
  (minimumHeight cutoff : Nat -> Nat)
  (endpointEpsilon mergeEpsilon : Nat -> Real)
  (width : Nat -> Nat)
  (hwidth : forall n, width n ∈ widths n)
  (hepsilon : Tendsto endpointEpsilon atTop (nhds 0)) :
-- imply
  Tendsto (fun n => mu.real (E.horizontalCrossingEvent (horizontalLeft (width n)) (horizontalRight (width n)) y (y + (rows n).height))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.horizontalEndpoint_tendsto_one E mu template widths horizontalLeft horizontalRight y minimumHeight cutoff endpointEpsilon mergeEpsilon rows width hwidth hepsilon

/--
[PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.VerticalEndpointExtension.verticalEndpoint_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma verticalEndpoint_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {y : Real}
  {rows : forall n, E.FiniteWidthEndpointMergeRow mu (template n) (widths n) horizontalLeft horizontalRight y (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n)}
  {extensions : forall n, (rows n).VerticalEndpointExtension (verticalBottom n) (verticalTop n) (x n) (minimumWidth n) (verticalEndpointEpsilon n)}
-- given
  (template : Nat -> Finset V)
  (widths : Nat -> Finset Nat)
  (horizontalLeft horizontalRight : Nat -> Int)
  (minimumHeight cutoff : Nat -> Nat)
  (endpointEpsilon mergeEpsilon : Nat -> Real)
  (verticalBottom verticalTop : Nat -> Nat -> Int)
  (x : Nat -> Real)
  (minimumWidth : Nat -> Nat)
  (verticalEndpointEpsilon : Nat -> Real)
  (step : Nat -> Nat)
  (hstep : forall n, step n <= (rows n).height)
  (hepsilon : Tendsto verticalEndpointEpsilon atTop (nhds 0)) :
-- imply
  Tendsto (fun n => mu.real (E.verticalCrossingEvent (x n) (x n + (extensions n).width) (verticalBottom n (step n)) (verticalTop n (step n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.VerticalEndpointExtension.verticalEndpoint_tendsto_one E mu template widths horizontalLeft horizontalRight y minimumHeight cutoff endpointEpsilon mergeEpsilon rows verticalBottom verticalTop x minimumWidth verticalEndpointEpsilon extensions step hstep hepsilon

/--
[PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.merge_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma merge_tendsto_zero_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {y : Real}
  {rows : forall n, E.FiniteWidthEndpointMergeRow mu (template n) (widths n) horizontalLeft horizontalRight y (minimumHeight n) (cutoff n) (endpointEpsilon n) (mergeEpsilon n)}
-- given
  (template : Nat -> Finset V)
  (widths : Nat -> Finset Nat)
  (horizontalLeft horizontalRight : Nat -> Int)
  (minimumHeight cutoff : Nat -> Nat)
  (endpointEpsilon mergeEpsilon : Nat -> Real)
  (step : Nat -> Nat)
  (hstep : forall n, step n <= (rows n).height)
  (q : Nat -> Fin 2 × (Fin 3 × Fin 3))
  (hepsilon : Tendsto mergeEpsilon atTop (nhds 0)) :
-- imply
  Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n) ((template n).image (P.shift (preferenceKingOffset (q n).2 + if (q n).1.val = 0 then 0 else verticalShift (step n)))) (rows n).radius)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.FiniteWidthEndpointMergeRow.merge_tendsto_zero E mu template widths horizontalLeft horizontalRight y minimumHeight cutoff endpointEpsilon mergeEpsilon rows step hstep q hepsilon

/--
[PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.centeredAdjacent_limit_of_pairMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma centeredAdjacent_limit_of_pairMerge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : forall n, E.CommonSquareNormalBoundaryBandData mu (S n) (margin n) (M n) (score n)}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (S : Nat -> Finset V)
  (margin M outerWidth outerHeight radius : Nat -> Nat)
  (score : Nat -> Real)
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n)
  (hMWidth : forall n, 2 * M n <= outerWidth n)
  (hMHeight : forall n, 2 * M n <= outerHeight n)
  (hwidth : forall n, 2 * margin n < outerWidth n - 2 * M n)
  (hheight : forall n, 2 * margin n < outerHeight n - 2 * M n)
  (hscore : Tendsto score atTop (nhds 1))
  (hscore_le : forall n, score n <= 1)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight (data n).zBottom (data n).zTop : Set V))) atTop (nhds 1))
  (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight (data n).zBottom (data n).zTop) ((P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight (data n).zBottom (data n).zTop).image (P.shift (preferenceKingOffset (q n).2 + if (q n).1.val = 0 then 0 else verticalShift (step n)))) (radius n))) atTop (nhds 0))
  (hconnector : forall n (v : PreferenceGridVertex (outerWidth n - 2 * M n) (outerHeight n - 2 * M n)), margin n <= v.1.val -> v.1.val + margin n < outerWidth n - 2 * M n -> margin n <= v.2.val -> v.2.val + margin n < outerHeight n - 2 * M n -> (P.shift (preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <= E.rectVertices (-(M n : Real)) ((M n : Real) + (outerWidth n - 2 * M n : Nat)) (-(M n : Real)) ((M n : Real) + (outerHeight n - 2 * M n : Nat))) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent 0 (outerWidth n) 0 (outerHeight n))) (mu.real (E.verticalCrossingEvent 0 (outerWidth n) 0 (outerHeight n + step n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.centeredAdjacent_limit_of_pairMerge E mu hFKG hTI S margin M outerWidth outerHeight radius score data step hstep hMWidth hMHeight hwidth hheight hscore hscore_le htemplateHit hmerge hconnector

/--
[PeriodicPlanarDualPair.canonicalAdjacentHeightArray_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma canonicalAdjacentHeightArray_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (width baseHeight K : Nat -> Nat)
  (hwidth : forall n, 10 * B < width n)
  (hheight : forall n, 10 * B < baseHeight n)
  (hverticalStart : Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (4 * B) (width n - 4 * B) 0 (baseHeight n))) atTop (nhds 1))
  (hhorizontalEnd : Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent 0 (width n) (4 * B) ((baseHeight n + (K n + 1) : Nat) - 4 * B))) atTop (nhds 1))
  (hprimal : forall k : Nat -> Nat, (forall n, k n < K n + 1) -> Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent 0 (width n) (4 * B) ((baseHeight n + k n : Nat) - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (4 * B) (width n - 4 * B) 0 (baseHeight n + (k n + 1) : Nat)))) atTop (nhds 1))
  (hdual : forall k : Nat -> Nat, (forall n, k n <= K n + 1) -> Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (4 * B) (width n - 4 * B) 0 (baseHeight n + k n : Nat))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent 0 (width n) (4 * B) ((baseHeight n + k n : Nat) - 4 * B)))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.canonicalAdjacentHeightArray_false D mu B hBpos hBp hBd width baseHeight K hwidth hheight hverticalStart hhorizontalEnd hprimal hdual

/--
[PeriodicPlaneEmbedding.exists_mixedAdjacentHeight_approxPreferredSide_crossing_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_mixedAdjacentHeight_approxPreferredSide_crossing_branch_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a0 b0 c0 d0 a1 b1 c1 d1 : Real}
  {step : Int}
  {width height : Nat}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hstep : 0 <= step)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (hepsilon : 0 <= epsilon)
  (source : PreferenceGridVertex width height -> Finset V)
  (bottom top left right : PreferenceGridVertex width height -> Real)
  (ha : a1 <= a0)
  (hb : b0 <= b1)
  (hc : c0 <= c1)
  (hd : d1 <= d0)
  (hsource : forall x, (source x : Set V) <= E.rectVertices a0 b0 c1 d1)
  (hbottomScore : forall x, bottom x = mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V) (E.rectBottomBoundaryVertices a1 b1 c1 d1)))
  (htopScore : forall x, top x = mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V) (E.rectTopBoundaryVertices a1 b1 c1 d1)))
  (hleftScore : forall x, left x = mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V) (E.rectLeftBoundaryVertices a0 b0 c0 d0)))
  (hrightScore : forall x, right x = mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V) (E.rectRightBoundaryVertices a0 b0 c0 d0)))
  (hbottom : forall i : Fin (width + 1), top (i, 0) <= bottom (i, 0) + epsilon)
  (htop : forall i : Fin (width + 1), bottom (i, Fin.last height) <= top (i, Fin.last height) + epsilon)
  (hleft : forall j : Fin (height + 1), right (0, j) <= left (0, j) + epsilon)
  (hright : forall j : Fin (height + 1), left (Fin.last width, j) <= right (Fin.last width, j) + epsilon) :
-- imply
  exists x xVertical xHorizontal : PreferenceGridVertex width height, KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) /\ KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) /\ ((1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <= bottom x + epsilon /\ let shifted := (source xVertical).image (P.shift (verticalShift step)) let Mtransfer := mu.real (E.rectanglePairMergeErrorUnion a1 b1 c1 d1 (source x) (source xVertical)) let Mjoin := mu.real (E.rectanglePairMergeErrorUnion a1 b1 c1 (d1 + step) (source x) shifted) bottom x * (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x - Mtransfer - epsilon) - Mjoin <= mu.real (E.verticalCrossingEvent a1 b1 c1 (d1 + step))) \/ (1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <= left x + epsilon /\ let M := mu.real (E.rectanglePairMergeErrorUnion a0 b0 c0 d0 (source x) (source xHorizontal)) left x * (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x - M - epsilon) - M <= mu.real (E.horizontalCrossingEvent a0 b0 c0 d0))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_mixedAdjacentHeight_approxPreferredSide_crossing_branch E mu hFKG hTI a0 b0 c0 d0 a1 b1 c1 d1 step hstep hwidth hheight epsilon hepsilon source bottom top left right ha hb hc hd hsource hbottomScore htopScore hleftScore hrightScore hbottom htop hleft hright

/--
[PeriodicPlaneEmbedding.mixedAdjacentHeightPreference_crossing_max_tendsto_one_of_pairMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma mixedAdjacentHeightPreference_crossing_max_tendsto_one_of_pairMerge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (template : Nat -> Finset V)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n)
  (radius : Nat -> Nat)
  (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n) ((template n).image (P.shift (preferenceKingOffset (q n).2 + if (q n).1.val = 0 then 0 else verticalShift (step n)))) (radius n))) atTop (nhds 0))
  (width height : Nat -> Nat)
  (hwidth : forall n, 0 < width n)
  (hheight : forall n, 0 < height n)
  (base : Nat -> Site 2)
  (a0 b0 c0 d0 a1 b1 c1 d1 epsilon : Nat -> Real)
  (bottom top left right : (n : Nat) -> PreferenceGridVertex (width n) (height n) -> Real)
  (hepsilon : Tendsto epsilon atTop (nhds 0))
  (hepsilon0 : forall n, 0 <= epsilon n)
  (ha : forall n, a1 n <= a0 n)
  (hb : forall n, b0 n <= b1 n)
  (hc : forall n, c0 n <= c1 n)
  (hd : forall n, d1 n <= d0 n)
  (hsource : forall n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) <= E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n))
  (hconnectorH : forall n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <= E.rectVertices (a0 n) (b0 n) (c0 n) (d0 n))
  (hconnectorV : forall n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <= E.rectVertices (a1 n) (b1 n) (c1 n) (d1 n))
  (hbottomScore : forall n v, bottom n v = mu.real (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n))))
  (htopScore : forall n v, top n v = mu.real (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n))))
  (hleftScore : forall n v, left n v = mu.real (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n))))
  (hrightScore : forall n v, right n v = mu.real (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n))))
  (hbottom : forall n i, top n (i, 0) <= bottom n (i, 0) + epsilon n)
  (htop : forall n i, bottom n (i, Fin.last (height n)) <= top n (i, Fin.last (height n)) + epsilon n)
  (hleft : forall n j, right n (0, j) <= left n (0, j) + epsilon n)
  (hright : forall n j, left n (Fin.last (width n), j) <= right n (Fin.last (width n), j) + epsilon n) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (a0 n) (b0 n) (c0 n) (d0 n))) (mu.real (E.verticalCrossingEvent (a1 n) (b1 n) (c1 n) (d1 n + step n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.mixedAdjacentHeightPreference_crossing_max_tendsto_one_of_pairMerge E mu hFKG hTI template htemplateHit step hstep radius hmerge width height hwidth hheight base a0 b0 c0 d0 a1 b1 c1 d1 epsilon bottom top left right hepsilon hepsilon0 ha hb hc hd hsource hconnectorH hconnectorV hbottomScore htopScore hleftScore hrightScore hbottom htop hleft hright

/--
[PeriodicPlaneEmbedding.exists_outward_mixed_approxPreferredSide_crossing_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_outward_mixed_approxPreferredSide_crossing_branch_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a0 b0 c0 d0 a1 b1 c1 d1 : Real}
  {pad : Int}
  {width height : Nat}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hpad : 0 <= pad)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (hepsilon : 0 <= epsilon)
  (source : PreferenceGridVertex width height -> Finset V)
  (bottom top left right : PreferenceGridVertex width height -> Real)
  (ha : a1 <= a0)
  (hb : b0 <= b1)
  (hc : c0 <= c1)
  (hd : d1 <= d0)
  (hsource : forall x, (source x : Set V) <= E.rectVertices a0 b0 c1 d1)
  (hbottomScore : forall x, bottom x = mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V) (E.rectBottomBoundaryVertices a1 b1 c1 d1)))
  (htopScore : forall x, top x = mu.real (E.rectSideConnectionEvent a1 b1 c1 d1 (source x : Set V) (E.rectTopBoundaryVertices a1 b1 c1 d1)))
  (hleftScore : forall x, left x = mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V) (E.rectLeftBoundaryVertices a0 b0 c0 d0)))
  (hrightScore : forall x, right x = mu.real (E.rectSideConnectionEvent a0 b0 c0 d0 (source x : Set V) (E.rectRightBoundaryVertices a0 b0 c0 d0)))
  (hbottom : forall i : Fin (width + 1), top (i, 0) <= bottom (i, 0) + epsilon)
  (htop : forall i : Fin (width + 1), bottom (i, Fin.last height) <= top (i, Fin.last height) + epsilon)
  (hleft : forall j : Fin (height + 1), right (0, j) <= left (0, j) + epsilon)
  (hright : forall j : Fin (height + 1), left (Fin.last width, j) <= right (Fin.last width, j) + epsilon) :
-- imply
  exists x xVertical xHorizontal : PreferenceGridVertex width height, KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) /\ KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) /\ ((1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <= bottom x + epsilon /\ let Ldown := (source x).image (P.shift (verticalShift (-pad))) let Rdown := (source xVertical).image (P.shift (verticalShift (-pad))) let Rup := (source xVertical).image (P.shift (verticalShift pad)) let Mtransfer := mu.real (E.rectanglePairMergeErrorUnion a1 b1 (c1 - pad) (d1 - pad) Ldown Rdown) let Mjoin := mu.real (E.rectanglePairMergeErrorUnion a1 b1 (c1 - pad) (d1 + pad) Ldown Rup) bottom x * (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x - Mtransfer - epsilon) - Mjoin <= mu.real (E.verticalCrossingEvent a1 b1 (c1 - pad) (d1 + pad))) \/ (1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <= left x + epsilon /\ let Lleft := (source x).image (P.shift (horizontalShift (-pad))) let Rleft := (source xHorizontal).image (P.shift (horizontalShift (-pad))) let Rright := (source xHorizontal).image (P.shift (horizontalShift pad)) let Mtransfer := mu.real (E.rectanglePairMergeErrorUnion (a0 - pad) (b0 - pad) c0 d0 Lleft Rleft) let Mjoin := mu.real (E.rectanglePairMergeErrorUnion (a0 - pad) (b0 + pad) c0 d0 Lleft Rright) left x * (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x - Mtransfer - epsilon) - Mjoin <= mu.real (E.horizontalCrossingEvent (a0 - pad) (b0 + pad) c0 d0))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_outward_mixed_approxPreferredSide_crossing_branch E mu hFKG hTI a0 b0 c0 d0 a1 b1 c1 d1 pad hpad hwidth hheight epsilon hepsilon source bottom top left right ha hb hc hd hsource hbottomScore htopScore hleftScore hrightScore hbottom htop hleft hright

/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_outwardMixedPreference_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_uniformTemplate_outwardMixedPreference_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (template : Nat -> Finset V)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
  (pad : Nat -> Int)
  (hpad : forall n, 0 <= pad n) :
-- imply
  exists radius : Nat -> Nat, forall (width height : Nat -> Nat) (hwidth : forall n, 0 < width n) (hheight : forall n, 0 < height n) (base : Nat -> Site 2) (a0 b0 c0 d0 a1 b1 c1 d1 epsilon : Nat -> Real) (bottom top left right : (n : Nat) -> PreferenceGridVertex (width n) (height n) -> Real), Tendsto epsilon atTop (nhds 0) -> (forall n, 0 <= epsilon n) -> (forall n, a1 n <= a0 n) -> (forall n, b0 n <= b1 n) -> (forall n, c0 n <= c1 n) -> (forall n, d1 n <= d0 n) -> (forall n (v : PreferenceGridVertex (width n) (height n)), ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) <= E.rectVertices (a0 n) (b0 n) (c1 n) (d1 n)) -> (forall n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + verticalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <= E.rectVertices (a1 n) (b1 n) (c1 n - pad n) (d1 n - pad n)) -> (forall n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + verticalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <= E.rectVertices (a1 n) (b1 n) (c1 n - pad n) (d1 n + pad n)) -> (forall n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + horizontalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <= E.rectVertices (a0 n - pad n) (b0 n - pad n) (c0 n) (d0 n)) -> (forall n (v : PreferenceGridVertex (width n) (height n)), (P.shift (base n + preferenceGridSite v + horizontalShift (-(pad n))) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <= E.rectVertices (a0 n - pad n) (b0 n + pad n) (c0 n) (d0 n)) -> (forall n v, bottom n v = mu.real (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectBottomBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) -> (forall n v, top n v = mu.real (E.rectSideConnectionEvent (a1 n) (b1 n) (c1 n) (d1 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectTopBoundaryVertices (a1 n) (b1 n) (c1 n) (d1 n)))) -> (forall n v, left n v = mu.real (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectLeftBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) -> (forall n v, right n v = mu.real (E.rectSideConnectionEvent (a0 n) (b0 n) (c0 n) (d0 n) ((template n).image (P.shift (base n + preferenceGridSite v)) : Set V) (E.rectRightBoundaryVertices (a0 n) (b0 n) (c0 n) (d0 n)))) -> (forall n i, top n (i, 0) <= bottom n (i, 0) + epsilon n) -> (forall n i, bottom n (i, Fin.last (height n)) <= top n (i, Fin.last (height n)) + epsilon n) -> (forall n j, right n (0, j) <= left n (0, j) + epsilon n) -> (forall n j, left n (Fin.last (width n), j) <= right n (Fin.last (width n), j) + epsilon n) -> exists branch : Nat -> Bool, Tendsto (fun n => if branch n then mu.real (E.verticalCrossingEvent (a1 n) (b1 n) (c1 n - pad n) (d1 n + pad n)) else mu.real (E.horizontalCrossingEvent (a0 n - pad n) (b0 n + pad n) (c0 n) (d0 n))) atTop (nhds 1) /\ Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a1 n) (b1 n) (c1 n - pad n) (d1 n + pad n))) (mu.real (E.horizontalCrossingEvent (a0 n - pad n) (b0 n + pad n) (c0 n) (d0 n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_outwardMixedPreference_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit pad hpad

/--
[PeriodicPlaneEmbedding.exists_uniformOrbitBoxOutwardMixedRadius_alignedExact_dualLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_uniformOrbitBoxOutwardMixedRadius_alignedExact_dualLimit_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {schedule : forall n, PairedAlignedMarginSchedule E Edual (family n) (familyDual n) (verticalRequirement n) (horizontalRequirement n)}
-- given
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (p pDual : Nat -> Real)
  (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
  (hpDual : Tendsto pDual atTop (nhds 1))
  (hpDual_le : forall n, pDual n <= 1)
  (pad : Nat -> Int)
  (hpad : forall n, 0 <= pad n) :
-- imply
  exists radius : Nat -> Nat, forall (k extentX extentY : Nat -> Nat) (data : forall n, AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (p n) (pDual n) (family n) (familyDual n) (schedule n) (k n) (extentX n) (extentY n)), (forall n, PairedAlignedConnectorSlack E Edual (family n) (familyDual n) (schedule n) (max (radius n) n) (k n)) -> Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent (data n).raw.data.wideLeft (data n).raw.data.wideRight (0 - (pad n : Real)) ((extentY n : Real) + pad n))) (muDual.real (Edual.horizontalCrossingEvent (0 - (pad n : Real)) ((extentX n : Real) + pad n) 0 (extentY n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformOrbitBoxOutwardMixedRadius_alignedExact_dualLimit E Edual mu muDual hFKGDual hTIDual huniqueDual p pDual family familyDual verticalRequirement horizontalRequirement schedule hpDual hpDual_le pad hpad

/--
[PeriodicPlaneEmbedding.alignedExact_primalMixedAdjacent_limit_of_pairMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma alignedExact_primalMixedAdjacent_limit_of_pairMerge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {schedule : forall n, PairedAlignedMarginSchedule E Edual (family n) (familyDual n) (verticalRequirement n) (horizontalRequirement n)}
  {data : forall n, AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (p n) (pDual n) (family n) (familyDual n) (schedule n) (k n) (extentX n) (extentY n)}
  {slack : forall n, PairedAlignedConnectorSlack E Edual (family n) (familyDual n) (schedule n) (max (radius n) n) (k n)}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (p pDual : Nat -> Real)
  (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
  (k extentX extentY step radius : Nat -> Nat)
  (hp : Tendsto p atTop (nhds 1))
  (hp_le : forall n, p n <= 1)
  (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (P.orbitBox n) ((P.orbitBox n).image (P.shift (preferenceKingOffset (q n).2 + if (q n).1.val = 0 then 0 else verticalShift (step n)))) (radius n))) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent 0 (extentX n) 0 (extentY n))) (mu.real (E.verticalCrossingEvent (data n).raw.data.wideLeft (data n).raw.data.wideRight 0 (extentY n + step n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.alignedExact_primalMixedAdjacent_limit_of_pairMerge E Edual mu muDual hFKG hTI hunique p pDual family familyDual verticalRequirement horizontalRequirement schedule k extentX extentY step radius data slack hp hp_le hmerge

/--
[PairedAdjacentBoundaryBandScheduleData.alignedExact_primalAdjacent_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma alignedExact_primalAdjacent_limit_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {step : Nat -> Int}
  {scheduleData : PairedAdjacentBoundaryBandScheduleData E Edual mu muDual step}
  {exact : forall n, AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (scheduleData.score n) (scheduleData.scoreDual n) (scheduleData.family n) (scheduleData.familyDual n) (scheduleData.schedule n) (k n) (extentX n) (extentY n)}
  {slack : forall n, PairedAlignedConnectorSlack E Edual (scheduleData.family n) (scheduleData.familyDual n) (scheduleData.schedule n) (max (scheduleData.radius n) n) (k n)}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (k extentX extentY : Nat -> Nat) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent 0 (extentX n) 0 (extentY n))) (mu.real (E.verticalCrossingEvent (exact n).raw.data.wideLeft (exact n).raw.data.wideRight 0 (extentY n + (step n).toNat)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAdjacentBoundaryBandScheduleData.alignedExact_primalAdjacent_limit scheduleData hFKG hTI hunique k extentX extentY exact slack

/--
[PairedAdjacentBoundaryBandScheduleData.exists_alignedExact_dualOutwardRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_alignedExact_dualOutwardRadius_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {step : Nat -> Int}
  {scheduleData : PairedAdjacentBoundaryBandScheduleData E Edual mu muDual step}
-- given
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (pad : Nat -> Int)
  (hpad : forall n, 0 <= pad n) :
-- imply
  exists radius : Nat -> Nat, forall (k extentX extentY : Nat -> Nat) (exact : forall n, AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (scheduleData.score n) (scheduleData.scoreDual n) (scheduleData.family n) (scheduleData.familyDual n) (scheduleData.schedule n) (k n) (extentX n) (extentY n)), (forall n, PairedAlignedConnectorSlack E Edual (scheduleData.family n) (scheduleData.familyDual n) (scheduleData.schedule n) (max (radius n) n) (k n)) -> Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent (exact n).raw.data.wideLeft (exact n).raw.data.wideRight (0 - (pad n : Real)) ((extentY n : Real) + pad n))) (muDual.real (Edual.horizontalCrossingEvent (0 - (pad n : Real)) ((extentX n : Real) + pad n) 0 (extentY n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAdjacentBoundaryBandScheduleData.exists_alignedExact_dualOutwardRadius scheduleData hFKGDual hTIDual huniqueDual pad hpad

/--
[PeriodicPlaneEmbedding.orbitBoxCoordinateBound_mono_adaptive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma orbitBoxCoordinateBound_mono_adaptive_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {n m : Nat}
  {i : Fin 2}
-- given
  (hnm : n <= m) :
-- imply
  E.orbitBoxCoordinateBound n i <= E.orbitBoxCoordinateBound m i := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.orbitBoxCoordinateBound_mono_adaptive E hnm i

/--
[PeriodicPlaneEmbedding.connectorMarginRequirement_mono_adaptive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma connectorMarginRequirement_mono_adaptive_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {radius radius' : Nat}
-- given
  (h : radius <= radius') :
-- imply
  E.connectorMarginRequirement radius <= E.connectorMarginRequirement radius' := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.connectorMarginRequirement_mono_adaptive E h

/--
[PairedAlignedConnectorSlack.restrictRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma restrictRadius_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {radius radius' k : Nat}
  {slack : PairedAlignedConnectorSlack E Edual family familyDual schedule radius' k}
-- given
  (h : radius <= radius') :
-- imply
  PairedAlignedConnectorSlack E Edual family familyDual schedule radius k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAlignedConnectorSlack.restrictRadius E Edual h slack

/--
[PairedAdjacentBoundaryBandScheduleData.exists_crossNestedOutwardData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_crossNestedOutwardData_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {step : Nat -> Int}
  {scheduleData : PairedAdjacentBoundaryBandScheduleData E Edual mu muDual step}
  {padding : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (pad : Nat -> Int)
  (hpad : forall n, 0 <= pad n)
  (lowerX lowerY : Nat -> Nat) :
-- imply
  exists data : PairedAdjacentCrossNestedOutwardData E Edual mu muDual scheduleData pad padding, (forall n, lowerX n <= (data.triple n).currentX) /\ (forall n, lowerY n <= (data.triple n).currentY) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAdjacentBoundaryBandScheduleData.exists_crossNestedOutwardData scheduleData hTI hFKGDual hTIDual huniqueDual pad hpad padding lowerX lowerY

/--
[PairedAdjacentCrossNestedOutwardData.local_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma local_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {step : Nat -> Int}
  {scheduleData : PairedAdjacentBoundaryBandScheduleData E Edual mu muDual step}
  {pad : Nat -> Int}
  {padding : Nat}
  {data : PairedAdjacentCrossNestedOutwardData E Edual mu muDual scheduleData pad padding}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent 0 (data.triple n).currentX 0 (data.triple n).currentY)) (mu.real (E.verticalCrossingEvent (data.triple n).current.raw.data.wideLeft (data.triple n).current.raw.data.wideRight 0 ((data.triple n).currentY + (step n).toNat)))) atTop (nhds 1) /\ Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent (data.triple n).previous.raw.data.wideLeft (data.triple n).previous.raw.data.wideRight (0 - (pad n : Real)) (((data.triple n).previousY : Real) + pad n))) (muDual.real (Edual.horizontalCrossingEvent (0 - (pad n : Real)) (((data.triple n).previousX : Real) + pad n) 0 (data.triple n).previousY))) atTop (nhds 1) /\ Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent (data.triple n).next.raw.data.wideLeft (data.triple n).next.raw.data.wideRight (0 - (pad n : Real)) (((data.triple n).nextY : Real) + pad n))) (muDual.real (Edual.horizontalCrossingEvent (0 - (pad n : Real)) (((data.triple n).nextX : Real) + pad n) 0 (data.triple n).nextY))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAdjacentCrossNestedOutwardData.local_limits data hFKG hTI hunique

/--
[PairedAdjacentCrossNestedOutwardData.shifted_matched_inequalities](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma shifted_matched_inequalities_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {step : Nat -> Int}
  {scheduleData : PairedAdjacentBoundaryBandScheduleData D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) step}
  {pad : Nat -> Int}
  {padding : Nat}
  {data : PairedAdjacentCrossNestedOutwardData D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) scheduleData pad padding}
  {B : Real}
-- given
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hpadding : 4 * B <= (padding : Real))
  (hcurrentX : forall n, 10 * B < (data.triple n).currentX)
  (hcurrentY : forall n, 10 * B < (data.triple n).currentY) :
-- imply
  (forall n, mu.real (D.primalEmbedding.horizontalCrossingEvent 0 (data.triple n).currentX 0 (data.triple n).currentY) + (D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent (data.triple n).previous.raw.data.wideLeft (data.triple n).previous.raw.data.wideRight 0 (data.triple n).previousY) <= 1) /\ (forall n, mu.real (D.primalEmbedding.verticalCrossingEvent (data.triple n).current.raw.data.wideLeft (data.triple n).current.raw.data.wideRight 0 (data.triple n).currentY) + (D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent 0 (data.triple n).nextX 0 (data.triple n).nextY) <= 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAdjacentCrossNestedOutwardData.shifted_matched_inequalities D mu data hTIDual B hBpos hBp hBd hpadding hcurrentX hcurrentY

/--
[adjacent_height_array_contradiction_of_primal_dual_bounded_limits_of_bounded_matches](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma adjacent_height_array_contradiction_of_primal_dual_bounded_limits_of_bounded_matches_eq
  [DecidableEq V]
  [DecidableEq W]
-- given
  (horizontal vertical dualVertical dualHorizontal : Nat -> Nat -> Real)
  (K : Nat -> Nat)
  (hhorizontal_nonneg : forall n k, 0 <= horizontal n k)
  (hvertical_nonneg : forall n k, 0 <= vertical n k)
  (hhorizontal_le_one : forall n k, horizontal n k <= 1)
  (hvertical_le_one : forall n k, vertical n k <= 1)
  (hvertical_start : Tendsto (fun n => vertical n 0) atTop (nhds 1))
  (hhorizontal_end : Tendsto (fun n => horizontal n (K n + 1)) atTop (nhds 1))
  (hmatchHorizontal : forall n k, k <= K n + 1 -> horizontal n k + dualVertical n k <= 1)
  (hmatchVertical : forall n k, k <= K n + 1 -> vertical n k + dualHorizontal n k <= 1)
  (hprimalLimits : forall k : Nat -> Nat, (forall n, k n < K n + 1) -> Tendsto (fun n => max (horizontal n (k n)) (vertical n (k n + 1))) atTop (nhds 1))
  (hdualLimits : forall k : Nat -> Nat, (forall n, k n <= K n + 1) -> Tendsto (fun n => max (dualVertical n (k n)) (dualHorizontal n (k n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.adjacent_height_array_contradiction_of_primal_dual_bounded_limits_of_bounded_matches horizontal vertical dualVertical dualHorizontal K hhorizontal_nonneg hvertical_nonneg hhorizontal_le_one hvertical_le_one hvertical_start hhorizontal_end hmatchHorizontal hmatchVertical hprimalLimits hdualLimits

/--
[shifted_crossNested_array_contradiction_of_bounded_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma shifted_crossNested_array_contradiction_of_bounded_limits_eq
  [DecidableEq V]
  [DecidableEq W]
-- given
  (horizontal vertical dualVertical dualHorizontal : Nat -> Nat -> Real)
  (K : Nat -> Nat)
  (hhorizontal_nonneg : forall n k, 0 <= horizontal n k)
  (hvertical_nonneg : forall n k, 0 <= vertical n k)
  (hhorizontal_le_one : forall n k, horizontal n k <= 1)
  (hvertical_le_one : forall n k, vertical n k <= 1)
  (hvertical_start : Tendsto (fun n => vertical n 0) atTop (nhds 1))
  (hhorizontal_end : Tendsto (fun n => horizontal n (2 * (K n + 1) + 2)) atTop (nhds 1))
  (hmatchHorizontal : forall n k, k < 2 * (K n + 1) + 2 -> horizontal n (k + 1) + dualVertical n k <= 1)
  (hmatchVertical : forall n k, k < 2 * (K n + 1) + 2 -> vertical n k + dualHorizontal n (k + 1) <= 1)
  (hprimalLimits : forall k : Nat -> Nat, (forall n, k n < K n + 1) -> Tendsto (fun n => max (horizontal n (2 * k n + 2)) (vertical n (2 * k n + 2))) atTop (nhds 1))
  (hdualLimits : forall k : Nat -> Nat, (forall n, k n <= K n + 1) -> Tendsto (fun n => max (dualVertical n (2 * k n + 1)) (dualHorizontal n (2 * k n + 1))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.shifted_crossNested_array_contradiction_of_bounded_limits horizontal vertical dualVertical dualHorizontal K hhorizontal_nonneg hvertical_nonneg hhorizontal_le_one hvertical_le_one hvertical_start hhorizontal_end hmatchHorizontal hmatchVertical hprimalLimits hdualLimits

/--
[AlignedCrossNestedPairedChain.extentX_eq_of_zero_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma extentX_eq_of_zero_eq_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding length : Nat}
  {first second : AlignedCrossNestedPairedChain E Edual mu muDual S Sdual p pDual family familyDual schedule k padding length}
-- given
  (hzero : first.extentX 0 = second.extentX 0) :
-- imply
  forall j, j <= length -> first.extentX j = second.extentX j := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedChain.extentX_eq_of_zero_eq first second hzero

/--
[AlignedCrossNestedPairedChain.extentY_eq_terminal_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma extentY_eq_terminal_add_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding length : Nat}
  {data : AlignedCrossNestedPairedChain E Edual mu muDual S Sdual p pDual family familyDual schedule k padding length}
  {j : Nat}
-- given
  (hj : j <= length) :
-- imply
  data.extentY j = data.extentY length + 2 * padding * (length - j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedChain.extentY_eq_terminal_add data hj

/--
[AlignedCrossNestedPairedChain.extentY_eq_of_terminal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma extentY_eq_of_terminal_eq_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding length : Nat}
  {first second : AlignedCrossNestedPairedChain E Edual mu muDual S Sdual p pDual family familyDual schedule k padding length}
-- given
  (hterminal : first.extentY length = second.extentY length) :
-- imply
  forall j, j <= length -> first.extentY j = second.extentY j := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedChain.extentY_eq_of_terminal_eq first second hterminal

/--
[exists_alignedCrossNestedPairedChain_at_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_alignedCrossNestedPairedChain_at_endpoints_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding length : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  exists thresholdX thresholdY : Nat, forall (initialX terminalY : Nat), thresholdX <= initialX -> thresholdY <= terminalY -> exists data : AlignedCrossNestedPairedChain E Edual mu muDual S Sdual p pDual family familyDual schedule k padding length, data.extentX 0 = initialX /\ data.extentY length = terminalY /\ (forall j, initialX <= data.extentX j) /\ forall j, terminalY <= data.extentY j := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_alignedCrossNestedPairedChain_at_endpoints E Edual mu muDual hTI hTIDual family familyDual schedule k padding length

/--
[exists_alignedCrossNestedPairedChain_horizontalEnd_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_alignedCrossNestedPairedChain_horizontalEnd_gt_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding length : Nat}
  {B : Real}
  {lowerX lowerY : Nat}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (hlowerX : 3 * B < 3 * (lowerX : Real))
  (hepsilon : 0 < epsilon) :
-- imply
  exists data : AlignedCrossNestedPairedChain E Edual mu muDual S Sdual p pDual family familyDual schedule k padding length, (forall j, lowerX <= data.extentX j) /\ (forall j, lowerY <= data.extentY j) /\ 1 - epsilon < mu.real (E.horizontalCrossingEvent 0 (data.extentX length) 0 (data.extentY length)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_alignedCrossNestedPairedChain_horizontalEnd_gt E Edual mu muDual hFKG hTI hunique hTIDual family familyDual schedule k padding length B hB0 hB lowerX lowerY hlowerX hepsilon

/--
[exists_alignedCrossNestedPairedChain_verticalStart_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_alignedCrossNestedPairedChain_verticalStart_gt_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding length : Nat}
  {B : Real}
  {lowerX lowerY : Nat}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (hlowerY : 3 * B < 3 * (lowerY : Real))
  (hepsilon : 0 < epsilon) :
-- imply
  exists data : AlignedCrossNestedPairedChain E Edual mu muDual S Sdual p pDual family familyDual schedule k padding length, (forall j, lowerX <= data.extentX j) /\ (forall j, lowerY <= data.extentY j) /\ 1 - epsilon < mu.real (E.verticalCrossingEvent (data.level 0).raw.data.wideLeft (data.level 0).raw.data.wideRight 0 (data.extentY 0)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_alignedCrossNestedPairedChain_verticalStart_gt E Edual mu muDual hFKG hTI hunique hTIDual family familyDual schedule k padding length B hB0 hB lowerX lowerY hlowerY hepsilon

/--
[opposedEndpointVerticalScore_mono_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma opposedEndpointVerticalScore_mono_width_eq
  [DecidableEq V]
  [DecidableEq W]
  {width width' height : Nat}
-- given
  (hwidth : width <= width') :
-- imply
  opposedEndpointVerticalScore width height <= opposedEndpointVerticalScore width' height := by
-- proof
  apply StatMech.FK.PeriodicPlanar.opposedEndpointVerticalScore_mono_width hwidth

/--
[opposedEndpointVerticalScore_anti_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma opposedEndpointVerticalScore_anti_height_eq
  [DecidableEq V]
  [DecidableEq W]
  {width height height' : Nat}
-- given
  (hheight : height <= height') :
-- imply
  opposedEndpointVerticalScore width height' <= opposedEndpointVerticalScore width height := by
-- proof
  apply StatMech.FK.PeriodicPlanar.opposedEndpointVerticalScore_anti_height hheight

/--
[opposedEndpointHorizontalScore_anti_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma opposedEndpointHorizontalScore_anti_width_eq
  [DecidableEq V]
  [DecidableEq W]
  {width width' height : Nat}
-- given
  (hwidth : width <= width') :
-- imply
  opposedEndpointHorizontalScore width' height <= opposedEndpointHorizontalScore width height := by
-- proof
  apply StatMech.FK.PeriodicPlanar.opposedEndpointHorizontalScore_anti_width hwidth

/--
[opposedEndpointHorizontalScore_mono_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma opposedEndpointHorizontalScore_mono_height_eq
  [DecidableEq V]
  [DecidableEq W]
  {width height height' : Nat}
-- given
  (hheight : height <= height') :
-- imply
  opposedEndpointHorizontalScore width height <= opposedEndpointHorizontalScore width height' := by
-- proof
  apply StatMech.FK.PeriodicPlanar.opposedEndpointHorizontalScore_mono_height hheight

/--
[exists_opposedEndpointVerticalSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_opposedEndpointVerticalSelector_eq
  [DecidableEq V]
  [DecidableEq W]
-- given
  (height minimumWidth : Nat -> Nat) :
-- imply
  exists width : Nat -> Nat, (forall n, minimumWidth n <= width n) /\ Tendsto (fun n => opposedEndpointVerticalScore (width n) (height n)) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_opposedEndpointVerticalSelector height minimumWidth

/--
[exists_opposedEndpointHorizontalSelector](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_opposedEndpointHorizontalSelector_eq
  [DecidableEq V]
  [DecidableEq W]
-- given
  (width minimumHeight : Nat -> Nat) :
-- imply
  exists height : Nat -> Nat, (forall n, minimumHeight n <= height n) /\ Tendsto (fun n => opposedEndpointHorizontalScore (width n) (height n)) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_opposedEndpointHorizontalSelector width minimumHeight

/--
[opposedEndpointScores_not_simultaneously_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma opposedEndpointScores_not_simultaneously_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
-- given
  (width height : Nat -> Nat) :
-- imply
  ¬ (Tendsto (fun n => opposedEndpointVerticalScore (width n) (height n)) atTop (nhds 1) /\ Tendsto (fun n => opposedEndpointHorizontalScore (width n) (height n)) atTop (nhds 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.opposedEndpointScores_not_simultaneously_tendsto_one width height

/--
[exists_alignedCrossNestedPairedChain_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_alignedCrossNestedPairedChain_ge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding length lowerX lowerY : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  exists data : AlignedCrossNestedPairedChain E Edual mu muDual S Sdual p pDual family familyDual schedule k padding length, (forall j, lowerX <= data.extentX j) /\ (forall j, lowerY <= data.extentY j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_alignedCrossNestedPairedChain_ge E Edual mu muDual hTI hTIDual family familyDual schedule k padding length lowerX lowerY

/--
[nonempty_alignedCrossNestedPairedChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma nonempty_alignedCrossNestedPairedChain_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding length : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  Nonempty (AlignedCrossNestedPairedChain E Edual mu muDual S Sdual p pDual family familyDual schedule k padding length) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.nonempty_alignedCrossNestedPairedChain E Edual mu muDual hTI hTIDual family familyDual schedule k padding length

/--
[PairedAdjacentBoundaryBandScheduleData.exists_crossNestedOutwardArrayData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_crossNestedOutwardArrayData_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {step : Nat -> Int}
  {scheduleData : PairedAdjacentBoundaryBandScheduleData E Edual mu muDual step}
  {padding : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (K lowerX lowerY : Nat -> Nat) :
-- imply
  exists data : PairedAdjacentCrossNestedOutwardArrayData E Edual mu muDual scheduleData padding K, (forall n j, lowerX n <= (data.chain n).extentX j) /\ (forall n j, lowerY n <= (data.chain n).extentY j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAdjacentBoundaryBandScheduleData.exists_crossNestedOutwardArrayData scheduleData hTI hFKGDual hTIDual huniqueDual padding K lowerX lowerY

/--
[PairedAdjacentCrossNestedOutwardArrayData.even_odd_local_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma even_odd_local_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {step : Nat -> Int}
  {scheduleData : PairedAdjacentBoundaryBandScheduleData E Edual mu muDual step}
  {padding : Nat}
  {K : Nat -> Nat}
  {data : PairedAdjacentCrossNestedOutwardArrayData E Edual mu muDual scheduleData padding K}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  (forall k : Nat -> Nat, Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent 0 ((data.chain n).extentX (2 * k n + 2)) 0 ((data.chain n).extentY (2 * k n + 2)))) (mu.real (E.verticalCrossingEvent ((data.chain n).level (2 * k n + 2)).raw.data.wideLeft ((data.chain n).level (2 * k n + 2)).raw.data.wideRight 0 (((data.chain n).extentY (2 * k n + 2)) + (step n).toNat)))) atTop (nhds 1)) /\ (forall k : Nat -> Nat, Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent ((data.chain n).level (2 * k n + 1)).raw.data.wideLeft ((data.chain n).level (2 * k n + 1)).raw.data.wideRight 0 ((data.chain n).extentY (2 * k n + 1)))) (muDual.real (Edual.horizontalCrossingEvent 0 ((data.chain n).extentX (2 * k n + 1)) 0 ((data.chain n).extentY (2 * k n + 1))))) atTop (nhds 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAdjacentCrossNestedOutwardArrayData.even_odd_local_limits data hFKG hTI hunique

/--
[AlignedExactExtentPairedMixedBoundaryScores.shifted_matched_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma shifted_matched_pair_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : D.primalEmbedding.NormalBoundaryBandFamily mu S p}
  {familyDual : D.dualEmbedding.NormalBoundaryBandFamily (D.dualMeasure mu) Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule D.primalEmbedding D.dualEmbedding family familyDual verticalRequirement horizontalRequirement}
  {k lowerX lowerY upperX upperY padding : Nat}
  {lower : AlignedExactExtentPairedMixedBoundaryScores D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) S Sdual p pDual family familyDual schedule k lowerX lowerY}
  {upper : AlignedExactExtentPairedMixedBoundaryScores D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) S Sdual p pDual family familyDual schedule k upperX upperY}
  {B : Real}
-- given
  (hnextX : (upperX : Int) = lower.raw.wideRightInt - lower.raw.wideLeftInt + 2 * padding)
  (hnextY : lowerY = upperY + 2 * padding)
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hpadding : 4 * B <= (padding : Real))
  (hlowerX : 10 * B < lowerX)
  (hlowerY : 10 * B < lowerY)
  (hupperX : 10 * B < upperX)
  (hupperY : 10 * B < upperY) :
-- imply
  mu.real (D.primalEmbedding.horizontalCrossingEvent 0 upperX 0 upperY) + (D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent lower.raw.data.wideLeft lower.raw.data.wideRight 0 lowerY) <= 1 /\ mu.real (D.primalEmbedding.verticalCrossingEvent lower.raw.data.wideLeft lower.raw.data.wideRight 0 lowerY) + (D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent 0 upperX 0 upperY) <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.shifted_matched_pair D mu lower upper hnextX hnextY hTIDual B hBpos hBp hBd hpadding hlowerX hlowerY hupperX hupperY

/--
[PairedAdjacentCrossNestedOutwardArrayData.false_of_endpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma false_of_endpoints_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {scheduleData : PairedAdjacentBoundaryBandScheduleData D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) (fun _ => 0)}
  {padding : Nat}
  {K : Nat -> Nat}
  {data : PairedAdjacentCrossNestedOutwardArrayData D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) scheduleData padding K}
  {B : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hpadding : 4 * B <= (padding : Real))
  (hextentX : forall n j, 10 * B < (data.chain n).extentX j)
  (hextentY : forall n j, 10 * B < (data.chain n).extentY j)
  (hverticalStart : Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent ((data.chain n).level 0).raw.data.wideLeft ((data.chain n).level 0).raw.data.wideRight 0 ((data.chain n).extentY 0))) atTop (nhds 1))
  (hhorizontalEnd : Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent 0 ((data.chain n).extentX (2 * (K n + 1) + 2)) 0 ((data.chain n).extentY (2 * (K n + 1) + 2)))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAdjacentCrossNestedOutwardArrayData.false_of_endpoints D mu data hFKG hTI hunique hTIDual B hBpos hBp hBd hpadding hextentX hextentY hverticalStart hhorizontalEnd

/--
[PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_horizontalEndpoint_rebuild](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_horizontalEndpoint_rebuild_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {preparation : D.CrossNestedOutwardArrayPreparation mu}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) :
-- imply
  exists rebuilt : D.CrossNestedOutwardArrayPreparation mu, Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent 0 ((rebuilt.array.chain n).extentX (2 * (n + 1) + 2)) 0 ((rebuilt.array.chain n).extentY (2 * (n + 1) + 2)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_horizontalEndpoint_rebuild D mu preparation hFKG hTI hunique hTIDual

/--
[PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_verticalEndpoint_rebuild_at_error](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_verticalEndpoint_rebuild_at_error_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {preparation : D.CrossNestedOutwardArrayPreparation mu}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
  (epsilon : Nat -> Real)
  (hepsilon : forall n, 0 < epsilon n)
  (hepsilonZero : Tendsto epsilon atTop (nhds 0)) :
-- imply
  exists rebuilt : D.CrossNestedOutwardArrayPreparation mu, (forall n, 1 - epsilon n < mu.real (D.primalEmbedding.verticalCrossingEvent ((rebuilt.array.chain n).level 0).raw.data.wideLeft ((rebuilt.array.chain n).level 0).raw.data.wideRight 0 ((rebuilt.array.chain n).extentY 0))) /\ Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent ((rebuilt.array.chain n).level 0).raw.data.wideLeft ((rebuilt.array.chain n).level 0).raw.data.wideRight 0 ((rebuilt.array.chain n).extentY 0))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_verticalEndpoint_rebuild_at_error D mu preparation hFKG hTI hunique hTIDual epsilon hepsilon hepsilonZero

/--
[PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_verticalEndpoint_rebuild](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_verticalEndpoint_rebuild_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {preparation : D.CrossNestedOutwardArrayPreparation mu}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) :
-- imply
  exists rebuilt : D.CrossNestedOutwardArrayPreparation mu, Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent ((rebuilt.array.chain n).level 0).raw.data.wideLeft ((rebuilt.array.chain n).level 0).raw.data.wideRight 0 ((rebuilt.array.chain n).extentY 0))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.CrossNestedOutwardArrayPreparation.exists_verticalEndpoint_rebuild D mu preparation hFKG hTI hunique hTIDual

/--
[PeriodicPlanarDualPair.nonempty_crossNestedOutwardArrayPreparation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma nonempty_crossNestedOutwardArrayPreparation_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG (D.dualMeasure mu))
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
  (huniqueDual : (D.dualMeasure mu) {eta | Pdual.HasUniqueInfiniteCluster eta} = 1) :
-- imply
  Nonempty (D.CrossNestedOutwardArrayPreparation mu) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.nonempty_crossNestedOutwardArrayPreparation D mu hFKG hTI hunique hFKGDual hTIDual huniqueDual

/--
[PeriodicPlanarDualPair.exists_canonicalCrossNestedOutwardArrayPreparation_of_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma exists_canonicalCrossNestedOutwardArrayPreparation_of_common_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hcommon : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) Nonempty (D.CrossNestedOutwardArrayPreparation mu) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_canonicalCrossNestedOutwardArrayPreparation_of_common D hp hp1 hq hcommon

/--
[PeriodicPlanarDualPair.CrossNestedOutwardEndpointCertificate.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma false_eq_2
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : D.CrossNestedOutwardEndpointCertificate mu}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.CrossNestedOutwardEndpointCertificate.false D mu data hFKG hTI hunique hTIDual

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_crossNestedOutwardEndpointCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_crossNestedOutwardEndpointCertificate_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hcertificate : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 -> Nonempty (D.CrossNestedOutwardEndpointCertificate mu)) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_crossNestedOutwardEndpointCertificate D hp hp1 hq hcertificate


-- created on 2026-10-23
