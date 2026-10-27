import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAspectComparison.Part3
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.horizontalCrossing_translate_measureReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma horizontalCrossing_translate_measureReal_eq_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Site 2}
  {a b c d : Real}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.horizontalCrossingEvent (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real))) = mu.real (E.horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_translate_measureReal_eq E mu hTI z a b c d

/--
[PeriodicPlaneEmbedding.verticalCrossing_translate_measureReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma verticalCrossing_translate_measureReal_eq_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Site 2}
  {a b c d : Real}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.verticalCrossingEvent (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real))) = mu.real (E.verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_translate_measureReal_eq E mu hTI z a b c d

/--
[PeriodicPlaneEmbedding.verticalCrossing_measureReal_le_translate_enlarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma verticalCrossing_measureReal_le_translate_enlarge_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Site 2}
  {a b a' b' c d : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (ha : a' <= a + (z 0 : Real))
  (hb : b + (z 0 : Real) <= b') :
-- imply
  mu.real (E.verticalCrossingEvent a b c d) <= mu.real (E.verticalCrossingEvent a' b' (c + (z 1 : Real)) (d + (z 1 : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_measureReal_le_translate_enlarge E mu hTI z ha hb

/--
[PeriodicPlaneEmbedding.horizontalCrossing_measureReal_le_translate_enlarge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma horizontalCrossing_measureReal_le_translate_enlarge_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Site 2}
  {a b c d c' d' : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hc : c' <= c + (z 1 : Real))
  (hd : d + (z 1 : Real) <= d') :
-- imply
  mu.real (E.horizontalCrossingEvent a b c d) <= mu.real (E.horizontalCrossingEvent (a + (z 0 : Real)) (b + (z 0 : Real)) c' d') := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_measureReal_le_translate_enlarge E mu hTI z hc hd

/--
[one_sub_nat_mul_one_sub_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma one_sub_nat_mul_one_sub_le_pow_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {x : Real}
  {n : Nat}
-- given
  (hx0 : 0 <= x)
  (hx1 : x <= 1) :
-- imply
  1 - (n : Real) * (1 - x) <= x ^ n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.one_sub_nat_mul_one_sub_le_pow x n hx0 hx1

/--
[finiteEventIntersection_measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma finiteEventIntersection_measurable_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  [MeasurableSpace Omega]
  {events : List (Set Omega)}
-- given
  (hmeasurable : forall A, A ∈ events -> MeasurableSet A) :
-- imply
  MeasurableSet (finiteEventIntersection events) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.finiteEventIntersection_measurable events hmeasurable

/--
[finiteEventIntersection_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma finiteEventIntersection_isIncreasing_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {events : List (Set (ConfigSpace E))}
-- given
  (hincreasing : forall A, A ∈ events -> IsIncreasing A) :
-- imply
  IsIncreasing (finiteEventIntersection events) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.finiteEventIntersection_isIncreasing events hincreasing

/--
[finiteEventIntersection_append](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma finiteEventIntersection_append_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {first second : List (Set Omega)} :
-- imply
  finiteEventIntersection (first ++ second) = finiteEventIntersection first ∩ finiteEventIntersection second := by
-- proof
  apply StatMech.FK.PeriodicPlanar.finiteEventIntersection_append first second

/--
[finiteEventIntersection_iterated_gluing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma finiteEventIntersection_iterated_gluing_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {n : Nat}
-- given
  (target : Nat -> Set Omega)
  (stepEvents : Nat -> List (Set Omega))
  (hstep : forall k, k < n -> finiteEventIntersection (target k :: stepEvents k) <= target (k + 1)) :
-- imply
  finiteEventIntersection (target 0 :: (List.range n).flatMap stepEvents) <= target n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.finiteEventIntersection_iterated_gluing target stepEvents n hstep

/--
[PeriodicPlaneEmbedding.finiteEventIntersection_overlapCrossings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma finiteEventIntersection_overlapCrossings_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B a l m b c d : ℝ}
-- given
  (hBpos : 0 < B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hal : a ≤ l)
  (hmb : m ≤ b)
  (hleft : a + 5 * B < m - 5 * B)
  (hright : l + 5 * B < b - 5 * B)
  (hheight : c + 5 * B < d - 5 * B) :
-- imply
  finiteEventIntersection [E.horizontalCrossingEvent a m (c + 4 * B) (d - 4 * B), E.horizontalCrossingEvent l b (c + 4 * B) (d - 4 * B), E.verticalCrossingEvent (l + 4 * B) (m - 4 * B) c d] ⊆ E.horizontalCrossingEvent a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.finiteEventIntersection_overlapCrossings E hBpos hB hal hmb hleft hright hheight

/--
[PeriodicPlaneEmbedding.iterated_overlapCrossings_glue_horizontal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma iterated_overlapCrossings_glue_horizontal_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {B a c d : Real}
  {n : Nat}
-- given
  (left right : Nat -> Real)
  (hBpos : 0 < B)
  (hB : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| <= B)
  (hal : forall k, k < n -> a <= left k)
  (hmb : forall k, k < n -> right k <= right (k + 1))
  (hleft : forall k, k < n -> a + 5 * B < right k - 5 * B)
  (hright : forall k, k < n -> left k + 5 * B < right (k + 1) - 5 * B)
  (hheight : forall k, k < n -> c - 4 * B * ((k + 1 : Nat) : Real) + 5 * B < d + 4 * B * ((k + 1 : Nat) : Real) - 5 * B) :
-- imply
  let lower : Nat -> Real := fun k => c - 4 * B * (k : Real) let upper : Nat -> Real := fun k => d + 4 * B * (k : Real) let target : Nat -> Set (ConfigSpace (Sym2 V)) := fun k => E.horizontalCrossingEvent a (right k) (lower k) (upper k) let stepEvents : Nat -> List (Set (ConfigSpace (Sym2 V))) := fun k => [E.horizontalCrossingEvent (left k) (right (k + 1)) (lower k) (upper k), E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B) (lower (k + 1)) (upper (k + 1))] finiteEventIntersection (target 0 :: (List.range n).flatMap stepEvents) <= target n := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iterated_overlapCrossings_glue_horizontal E B a c d left right n hBpos hB hal hmb hleft hright hheight

/--
[finiteEventIntersection_measureReal_ge_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma finiteEventIntersection_measureReal_ge_pow_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {s : Real}
  {events : List (Set (ConfigSpace (Sym2 V)))}
-- given
  (hFKG : IsFKG mu)
  (hs : 0 <= s)
  (hmeasurable : forall A, A ∈ events -> MeasurableSet A)
  (hincreasing : forall A, A ∈ events -> IsIncreasing A)
  (hlower : forall A, A ∈ events -> s <= mu.real A) :
-- imply
  s ^ events.length <= mu.real (finiteEventIntersection events) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.finiteEventIntersection_measureReal_ge_pow mu hFKG s hs events hmeasurable hincreasing hlower

/--
[finiteEventIntersection_iterated_gluing_measureReal_ge_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma finiteEventIntersection_iterated_gluing_measureReal_ge_pow_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {s : Real}
  {n : Nat}
-- given
  (hFKG : IsFKG mu)
  (hs : 0 <= s)
  (target : Nat -> Set (ConfigSpace (Sym2 V)))
  (stepEvents : Nat -> List (Set (ConfigSpace (Sym2 V))))
  (hstep : forall k, k < n -> finiteEventIntersection (target k :: stepEvents k) <= target (k + 1))
  (hmeasurable : forall A, A ∈ target 0 :: (List.range n).flatMap stepEvents -> MeasurableSet A)
  (hincreasing : forall A, A ∈ target 0 :: (List.range n).flatMap stepEvents -> IsIncreasing A)
  (hlower : forall A, A ∈ target 0 :: (List.range n).flatMap stepEvents -> s <= mu.real A) :
-- imply
  s ^ (target 0 :: (List.range n).flatMap stepEvents).length <= mu.real (target n) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.finiteEventIntersection_iterated_gluing_measureReal_ge_pow mu hFKG s hs target stepEvents n hstep hmeasurable hincreasing hlower

/--
[PeriodicPlaneEmbedding.overlapCrossings_measureReal_ge_cube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma overlapCrossings_measureReal_ge_cube_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B a l m b c d s : ℝ}
-- given
  (hFKG : IsFKG mu)
  (hs : 0 ≤ s)
  (hBpos : 0 < B)
  (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
  (hal : a ≤ l)
  (hmb : m ≤ b)
  (hleft : a + 5 * B < m - 5 * B)
  (hright : l + 5 * B < b - 5 * B)
  (hheight : c + 5 * B < d - 5 * B)
  (hfirst : s ≤ mu.real (E.horizontalCrossingEvent a m (c + 4 * B) (d - 4 * B)))
  (hsecond : s ≤ mu.real (E.horizontalCrossingEvent l b (c + 4 * B) (d - 4 * B)))
  (hconnector : s ≤ mu.real (E.verticalCrossingEvent (l + 4 * B) (m - 4 * B) c d)) :
-- imply
  s ^ 3 ≤ mu.real (E.horizontalCrossingEvent a b c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.overlapCrossings_measureReal_ge_cube E mu hFKG hs hBpos hB hal hmb hleft hright hheight hfirst hsecond hconnector

/--
[PeriodicPlaneEmbedding.iterated_overlapCrossings_measureReal_ge_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma iterated_overlapCrossings_measureReal_ge_pow_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B a c d : Real}
  {n : Nat}
  {s : Real}
-- given
  (hFKG : IsFKG mu)
  (left right : Nat -> Real)
  (hs : 0 <= s)
  (hBpos : 0 < B)
  (hB : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |E.coordinates (E.edgeArc hxy t - E.vertex x) i| <= B)
  (hal : forall k, k < n -> a <= left k)
  (hmb : forall k, k < n -> right k <= right (k + 1))
  (hleft : forall k, k < n -> a + 5 * B < right k - 5 * B)
  (hright : forall k, k < n -> left k + 5 * B < right (k + 1) - 5 * B)
  (hheight : forall k, k < n -> c - 4 * B * ((k + 1 : Nat) : Real) + 5 * B < d + 4 * B * ((k + 1 : Nat) : Real) - 5 * B)
  (hinitial : s <= mu.real (E.horizontalCrossingEvent a (right 0) c d))
  (hhorizontal : forall k, k < n -> s <= mu.real (E.horizontalCrossingEvent (left k) (right (k + 1)) (c - 4 * B * (k : Real)) (d + 4 * B * (k : Real))))
  (hvertical : forall k, k < n -> s <= mu.real (E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B) (c - 4 * B * ((k + 1 : Nat) : Real)) (d + 4 * B * ((k + 1 : Nat) : Real)))) :
-- imply
  s ^ (1 + 2 * n) <= mu.real (E.horizontalCrossingEvent a (right n) (c - 4 * B * (n : Real)) (d + 4 * B * (n : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.iterated_overlapCrossings_measureReal_ge_pow E mu hFKG B a c d left right n s hs hBpos hB hal hmb hleft hright hheight hinitial hhorizontal hvertical

/--
[PeriodicPlanarDualPair.CrossNestedOutwardPowerAspectComparison.nonempty_endpointCertificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma nonempty_endpointCertificate_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {comparison : D.CrossNestedOutwardPowerAspectComparison mu}
  {preparation : D.CrossNestedOutwardArrayPreparation mu}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu)) :
-- imply
  Nonempty (D.CrossNestedOutwardEndpointCertificate mu) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.CrossNestedOutwardPowerAspectComparison.nonempty_endpointCertificate D mu comparison preparation hFKG hTI hunique hTIDual

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_powerAspectComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_powerAspectComparison_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hcomparison : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 -> D.CrossNestedOutwardPowerAspectComparison mu) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_powerAspectComparison D hp hp1 hq hcomparison

/--
[PeriodicPlanarDualPair.strictDualNoCoexistence_of_powerAspectComparison_logisticCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma strictDualNoCoexistence_of_powerAspectComparison_logisticCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 <= q)
  (hcomparison : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 -> D.CrossNestedOutwardPowerAspectComparison mu)
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
-- imply
  StrictDualNoCoexistence (fun p => P.wiredPercolates p q) (fun p => Pdual.wiredPercolates p q) q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.strictDualNoCoexistence_of_powerAspectComparison_logisticCylinders D hconn hconnDual hq hcomparison hagrees

/--
[PeriodicPlanarDualPair.dualCritical_relation_of_bidirectionalDecay_powerAspectComparison_logisticCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma dualCritical_relation_of_bidirectionalDecay_powerAspectComparison_logisticCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {Hdual : PolynomialConnectionShells D.swap}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 <= q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
  (hdecayDual : SubcriticalTwoPointExponentialDecay Pdual q (Pdual.criticalPoint q))
  (hcomparison : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 -> D.CrossNestedOutwardPowerAspectComparison mu)
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_bidirectionalDecay_powerAspectComparison_logisticCylinders D H Hdual hconn hconnDual hq hdecay hdecayDual hcomparison hagrees

/--
[PeriodicPlanarDualPair.dualCritical_relation_of_bidirectionalDecay_aspectGluing_logisticCylinders](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean)
-/
@[path]
private lemma dualCritical_relation_of_bidirectionalDecay_aspectGluing_logisticCylinders_eq
  {V W : Type}
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {H : PolynomialConnectionShells D}
  {Hdual : PolynomialConnectionShells D.swap}
  {q : Real}
-- given
  (hconn : P.graph.Connected)
  (hconnDual : Pdual.graph.Connected)
  (hq : 1 <= q)
  (hdecay : SubcriticalTwoPointExponentialDecay P q (P.criticalPoint q))
  (hdecayDual : SubcriticalTwoPointExponentialDecay Pdual q (Pdual.criticalPoint q))
  (hgluing : forall (p : Real) (hp : 0 < p) (hp1 : p < 1), let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1 -> D.CrossNestedOutwardAspectGluing mu)
  (hagrees : P.FreeWiredIncreasingCylinderAgreementOffCountableAtLogistic q) :
-- imply
  dualParam (P.criticalPoint q) q = Pdual.criticalPoint q /\ (P.criticalPoint q / (1 - P.criticalPoint q)) * (Pdual.criticalPoint q / (1 - Pdual.criticalPoint q)) = q := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualCritical_relation_of_bidirectionalDecay_aspectGluing_logisticCylinders D H Hdual hconn hconnDual hq hdecay hdecayDual hgluing hagrees


-- created on 2026-10-23
