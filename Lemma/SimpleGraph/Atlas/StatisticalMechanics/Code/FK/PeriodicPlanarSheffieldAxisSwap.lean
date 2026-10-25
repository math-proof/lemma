import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAxisSwap.Part3
open Filter MeasureTheory Set SimpleGraph Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[siteAxisSwap_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma siteAxisSwap_zero_eq
  [DecidableEq V]
  [Countable V] :
-- imply
  siteAxisSwap (0 : Site 2) = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.siteAxisSwap_zero

/--
[siteAxisSwap_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma siteAxisSwap_add_eq
  [DecidableEq V]
  [Countable V]
  {z w : Site 2} :
-- imply
  siteAxisSwap (z + w) = siteAxisSwap z + siteAxisSwap w := by
-- proof
  apply StatMech.FK.PeriodicPlanar.siteAxisSwap_add z w

/--
[siteAxisSwap_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma siteAxisSwap_swap_eq
  [DecidableEq V]
  [Countable V]
  {z : Site 2} :
-- imply
  siteAxisSwap (siteAxisSwap z) = z := by
-- proof
  apply StatMech.FK.PeriodicPlanar.siteAxisSwap_swap z

/--
[axisSwapCoordinates_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma axisSwapCoordinates_apply_eq
  [DecidableEq V]
  [Countable V]
  {x : Fin 2 → Real}
  {i : Fin 2} :
-- imply
  axisSwapCoordinates x i = x (Fin.rev i) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.axisSwapCoordinates_apply x i

/--
[PeriodicPlaneEmbedding.axisSwap_vertexCoord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma axisSwap_vertexCoord_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x : V}
  {i : Fin 2} :
-- imply
  E.axisSwap.vertexCoord x i = E.vertexCoord x (Fin.rev i) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_vertexCoord E x i

/--
[PeriodicPlaneEmbedding.axisSwap_vertexCoord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma axisSwap_vertexCoord_zero_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x : V} :
-- imply
  E.axisSwap.vertexCoord x 0 = E.vertexCoord x 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_vertexCoord_zero E x

/--
[PeriodicPlaneEmbedding.axisSwap_vertexCoord_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma axisSwap_vertexCoord_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {x : V} :
-- imply
  E.axisSwap.vertexCoord x 1 = E.vertexCoord x 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_vertexCoord_one E x

/--
[PeriodicGraph.axisSwap_isTranslationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma axisSwap_isTranslationInvariant_eq
  [DecidableEq V]
  [Countable V]
  {P : PeriodicGraph V}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  P.axisSwap.IsTranslationInvariant mu := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.axisSwap_isTranslationInvariant P mu hTI

/--
[PeriodicPlaneEmbedding.axisSwap_verticalCrossingEvent_subset_horizontalCrossingEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma axisSwap_verticalCrossingEvent_subset_horizontalCrossingEvent_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {a b c d : Real} :
-- imply
  E.axisSwap.verticalCrossingEvent a b c d ⊆ E.horizontalCrossingEvent c d a b := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.axisSwap_verticalCrossingEvent_subset_horizontalCrossingEvent E a b c d

/--
[PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_of_axisSwap_finiteStripJoinedBoundaryArms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma horizontalCrossing_tendsto_one_of_axisSwap_finiteStripJoinedBoundaryArms_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {r c d : Nat → Real}
  {lower upper : Nat → Finset V}
-- given
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
  (hB0 : 0 ≤ B)
  (height : Nat → Nat)
  (hgap : ∀ n, 3 * B < d n - c n)
  (harms : Tendsto (fun n ↦ mu.real (E.axisSwap.finiteStripJoinedBoundaryArmEvent (r n) (c n) (d n) (height n) (lower n) (upper n))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n ↦ mu.real (E.horizontalCrossingEvent ((2 * c n + d n) / 3) ((c n + 2 * d n) / 3) (r n) (r n + height n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_tendsto_one_of_axisSwap_finiteStripJoinedBoundaryArms E mu B hB hB0 r c d height lower upper hgap harms

/--
[PeriodicPlaneEmbedding.exists_horizontalCrossing_measureReal_gt_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma exists_horizontalCrossing_measureReal_gt_of_unique_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r B s : Real}
  {t : Int}
  {m : Nat}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
  (ht : 3 * B < t)
  (hepsilon : 0 < epsilon) :
-- imply
  ∃ n : Nat, m ≤ n ∧ 1 - epsilon < mu.real (E.horizontalCrossingEvent ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3) r (r + n)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_horizontalCrossing_measureReal_gt_of_unique E mu hFKG hTI hunique r B s hB0 hB t ht m hepsilon

/--
[PeriodicPlaneEmbedding.exists_cofinal_horizontalCrossing_tendsto_one_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma exists_cofinal_horizontalCrossing_tendsto_one_of_unique_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r B s : Real}
  {t : Int}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxy u - E.vertex x) i| ≤ B)
  (ht : 3 * B < t) :
-- imply
  ∃ height : Nat → Nat, Tendsto height atTop atTop ∧ Tendsto (fun k => mu.real (E.horizontalCrossingEvent ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3) r (r + height k))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_cofinal_horizontalCrossing_tendsto_one_of_unique E mu hFKG hTI hunique r B s hB0 hB t ht

/--
[PeriodicPlanarDualPair.exists_cofinal_complementaryDual_horizontalCrossing_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAxisSwap.lean)
-/
@[path]
private lemma exists_cofinal_complementaryDual_horizontalCrossing_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  [DecidableEq W]
  [Countable W]
  {Pdual : PeriodicGraph W}
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r B s : Real}
  {t : Int}
-- given
  (hdualFKG : IsFKG (D.dualMeasure mu))
  (hTI : P.IsTranslationInvariant mu)
  (hdualUnique : D.dualMeasure mu {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hB0 : 0 ≤ B)
  (hB : ∀ {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| ≤ B)
  (ht : 3 * B < t) :
-- imply
  ∃ height : Nat → Nat, Tendsto height atTop atTop ∧ Tendsto (fun k => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3) r (r + height k))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_cofinal_complementaryDual_horizontalCrossing_tendsto_one D mu hdualFKG hTI hdualUnique r B s hB0 hB t ht


-- created on 2026-10-23
