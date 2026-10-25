/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAspectComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part9
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCrossingGluing.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictCriticalAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarStrictNoCoexistenceClosure.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAspectComparison
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V W : Type} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


theorem finiteEventIntersection_measurable {Omega : Type*}
    [MeasurableSpace Omega] (events : List (Set Omega))
    (hmeasurable : forall A, A ∈ events -> MeasurableSet A) :
    MeasurableSet (finiteEventIntersection events) := by
  induction events with
  | nil => simp [finiteEventIntersection]
  | cons A events ih =>
      rw [finiteEventIntersection]
      exact (hmeasurable A (by simp)).inter
        (ih (fun B hB => hmeasurable B (by simp [hB])))

theorem finiteEventIntersection_isIncreasing
    {E : Type*} (events : List (Set (ConfigSpace E)))
    (hincreasing : forall A, A ∈ events -> IsIncreasing A) :
    IsIncreasing (finiteEventIntersection events) := by
  induction events with
  | nil =>
      intro omega eta _homega _heta
      exact Set.mem_univ eta
  | cons A events ih =>
      rw [finiteEventIntersection]
      exact (hincreasing A (by simp)).inter
        (ih (fun B hB => hincreasing B (by simp [hB])))


theorem finiteEventIntersection_append {Omega : Type*}
    (first second : List (Set Omega)) :
    finiteEventIntersection (first ++ second) =
      finiteEventIntersection first ∩ finiteEventIntersection second := by
  induction first with
  | nil => simp [finiteEventIntersection]
  | cons A first ih =>
      simp only [List.cons_append, finiteEventIntersection, ih]
      exact (Set.inter_assoc _ _ _).symm


theorem finiteEventIntersection_iterated_gluing {Omega : Type*}
    (target : Nat -> Set Omega) (stepEvents : Nat -> List (Set Omega))
    (n : Nat)
    (hstep : forall k, k < n ->
      finiteEventIntersection (target k :: stepEvents k) <= target (k + 1)) :
    finiteEventIntersection
        (target 0 :: (List.range n).flatMap stepEvents) <= target n := by
  induction n with
  | zero =>
      simpa [finiteEventIntersection]
  | succ n ih =>
      have hprevious : finiteEventIntersection
          (target 0 :: (List.range n).flatMap stepEvents) <= target n :=
        ih (fun k hk => hstep k (by omega))
      intro omega homega
      have hsplit : omega ∈
          finiteEventIntersection
              (target 0 :: (List.range n).flatMap stepEvents) ∩
            finiteEventIntersection (stepEvents n) := by
        rw [<- finiteEventIntersection_append]
        simpa only [List.range_succ, List.flatMap_append,
          List.flatMap_singleton, List.cons_append] using homega
      apply hstep n (by omega)
      exact ⟨hprevious hsplit.1, hsplit.2⟩


theorem PeriodicPlaneEmbedding.finiteEventIntersection_overlapCrossings
    (E : PeriodicPlaneEmbedding P) {B a l m b c d : ℝ}
    (hBpos : 0 < B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    (hal : a ≤ l) (hmb : m ≤ b)
    (hleft : a + 5 * B < m - 5 * B)
    (hright : l + 5 * B < b - 5 * B)
    (hheight : c + 5 * B < d - 5 * B) :
    finiteEventIntersection
      [E.horizontalCrossingEvent a m (c + 4 * B) (d - 4 * B),
       E.horizontalCrossingEvent l b (c + 4 * B) (d - 4 * B),
       E.verticalCrossingEvent (l + 4 * B) (m - 4 * B) c d] ⊆
      E.horizontalCrossingEvent a b c d := by
  simpa [finiteEventIntersection] using
    E.overlapCrossings_glue_horizontal hBpos hB hal hmb
      hleft hright hheight


theorem PeriodicPlaneEmbedding.iterated_overlapCrossings_glue_horizontal
    (E : PeriodicPlaneEmbedding P) (B a c d : Real)
    (left right : Nat -> Real) (n : Nat)
    (hBpos : 0 < B)
    (hB : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| <= B)
    (hal : forall k, k < n -> a <= left k)
    (hmb : forall k, k < n -> right k <= right (k + 1))
    (hleft : forall k, k < n -> a + 5 * B < right k - 5 * B)
    (hright : forall k, k < n ->
      left k + 5 * B < right (k + 1) - 5 * B)
    (hheight : forall k, k < n ->
      c - 4 * B * ((k + 1 : Nat) : Real) + 5 * B <
        d + 4 * B * ((k + 1 : Nat) : Real) - 5 * B) :
    let lower : Nat -> Real := fun k => c - 4 * B * (k : Real)
    let upper : Nat -> Real := fun k => d + 4 * B * (k : Real)
    let target : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
      E.horizontalCrossingEvent a (right k) (lower k) (upper k)
    let stepEvents : Nat -> List (Set (ConfigSpace (Sym2 V))) := fun k =>
      [E.horizontalCrossingEvent (left k) (right (k + 1))
          (lower k) (upper k),
       E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B)
          (lower (k + 1)) (upper (k + 1))]
    finiteEventIntersection
        (target 0 :: (List.range n).flatMap stepEvents) <= target n := by
  dsimp only
  let lower : Nat -> Real := fun k => c - 4 * B * (k : Real)
  let upper : Nat -> Real := fun k => d + 4 * B * (k : Real)
  let target : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    E.horizontalCrossingEvent a (right k) (lower k) (upper k)
  let stepEvents : Nat -> List (Set (ConfigSpace (Sym2 V))) := fun k =>
    [E.horizontalCrossingEvent (left k) (right (k + 1))
        (lower k) (upper k),
     E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B)
        (lower (k + 1)) (upper (k + 1))]
  apply finiteEventIntersection_iterated_gluing target stepEvents n
  intro k hk
  have hlower : lower (k + 1) + 4 * B = lower k := by
    dsimp only [lower]
    push_cast
    ring
  have hupper : upper (k + 1) - 4 * B = upper k := by
    dsimp only [upper]
    push_cast
    ring
  have hlocal := E.finiteEventIntersection_overlapCrossings
    hBpos hB (hal k hk) (hmb k hk) (hleft k hk) (hright k hk)
      (hheight k hk)
  change finiteEventIntersection
      [E.horizontalCrossingEvent a (right k) (lower k) (upper k),
       E.horizontalCrossingEvent (left k) (right (k + 1))
          (lower k) (upper k),
       E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B)
          (lower (k + 1)) (upper (k + 1))] <=
    E.horizontalCrossingEvent a (right (k + 1))
      (lower (k + 1)) (upper (k + 1))
  rw [<- hlower, <- hupper]
  exact hlocal


theorem finiteEventIntersection_measureReal_ge_pow
    {V : Type*} (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (s : Real) (hs : 0 <= s)
    (events : List (Set (ConfigSpace (Sym2 V))))
    (hmeasurable : forall A, A ∈ events -> MeasurableSet A)
    (hincreasing : forall A, A ∈ events -> IsIncreasing A)
    (hlower : forall A, A ∈ events -> s <= mu.real A) :
    s ^ events.length <= mu.real (finiteEventIntersection events) := by
  induction events with
  | nil => simp [finiteEventIntersection]
  | cons A events ih =>
      have hAm : MeasurableSet A := hmeasurable A (by simp)
      have hAi : IsIncreasing A := hincreasing A (by simp)
      have htailm : MeasurableSet (finiteEventIntersection events) :=
        finiteEventIntersection_measurable events
          (fun B hB => hmeasurable B (by simp [hB]))
      have htaili : IsIncreasing (finiteEventIntersection events) :=
        finiteEventIntersection_isIncreasing events
          (fun B hB => hincreasing B (by simp [hB]))
      have htail := ih
        (fun B hB => hmeasurable B (by simp [hB]))
        (fun B hB => hincreasing B (by simp [hB]))
        (fun B hB => hlower B (by simp [hB]))
      calc
        s ^ (A :: events).length = s ^ events.length * s := by
          simp only [List.length_cons, pow_succ]
        _ <= mu.real (finiteEventIntersection events) * mu.real A := by
          exact mul_le_mul htail (hlower A (by simp)) hs measureReal_nonneg
        _ = mu.real A * mu.real (finiteEventIntersection events) :=
          mul_comm _ _
        _ <= mu.real (A ∩ finiteEventIntersection events) :=
          hFKG A (finiteEventIntersection events) hAm htailm hAi htaili
        _ = mu.real (finiteEventIntersection (A :: events)) := rfl


theorem finiteEventIntersection_iterated_gluing_measureReal_ge_pow
    {V : Type*} (mu : Measure (ConfigSpace (Sym2 V)))
    [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (s : Real) (hs : 0 <= s)
    (target : Nat -> Set (ConfigSpace (Sym2 V)))
    (stepEvents : Nat -> List (Set (ConfigSpace (Sym2 V)))) (n : Nat)
    (hstep : forall k, k < n ->
      finiteEventIntersection (target k :: stepEvents k) <= target (k + 1))
    (hmeasurable : forall A,
      A ∈ target 0 :: (List.range n).flatMap stepEvents -> MeasurableSet A)
    (hincreasing : forall A,
      A ∈ target 0 :: (List.range n).flatMap stepEvents -> IsIncreasing A)
    (hlower : forall A,
      A ∈ target 0 :: (List.range n).flatMap stepEvents -> s <= mu.real A) :
    s ^ (target 0 :: (List.range n).flatMap stepEvents).length <=
      mu.real (target n) := by
  calc
    s ^ (target 0 :: (List.range n).flatMap stepEvents).length <=
        mu.real (finiteEventIntersection
          (target 0 :: (List.range n).flatMap stepEvents)) :=
      finiteEventIntersection_measureReal_ge_pow mu hFKG s hs _
        hmeasurable hincreasing hlower
    _ <= mu.real (target n) := measureReal_mono
      (finiteEventIntersection_iterated_gluing target stepEvents n hstep)


theorem PeriodicPlaneEmbedding.overlapCrossings_measureReal_ge_cube
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) {B a l m b c d s : ℝ}
    (hs : 0 ≤ s)
    (hBpos : 0 < B)
    (hB : ∀ {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| ≤ B)
    (hal : a ≤ l) (hmb : m ≤ b)
    (hleft : a + 5 * B < m - 5 * B)
    (hright : l + 5 * B < b - 5 * B)
    (hheight : c + 5 * B < d - 5 * B)
    (hfirst : s ≤ mu.real
      (E.horizontalCrossingEvent a m (c + 4 * B) (d - 4 * B)))
    (hsecond : s ≤ mu.real
      (E.horizontalCrossingEvent l b (c + 4 * B) (d - 4 * B)))
    (hconnector : s ≤ mu.real
      (E.verticalCrossingEvent (l + 4 * B) (m - 4 * B) c d)) :
    s ^ 3 ≤ mu.real (E.horizontalCrossingEvent a b c d) := by
  let events : List (Set (ConfigSpace (Sym2 V))) :=
    [E.horizontalCrossingEvent a m (c + 4 * B) (d - 4 * B),
     E.horizontalCrossingEvent l b (c + 4 * B) (d - 4 * B),
     E.verticalCrossingEvent (l + 4 * B) (m - 4 * B) c d]
  have hintersection : s ^ events.length ≤
      mu.real (finiteEventIntersection events) :=
    finiteEventIntersection_measureReal_ge_pow mu hFKG s hs events
      (by
        intro A hA
        simp only [events, List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl | rfl
        · exact E.horizontalCrossingEvent_measurableSet _ _ _ _
        · exact E.horizontalCrossingEvent_measurableSet _ _ _ _
        · exact E.verticalCrossingEvent_measurableSet _ _ _ _)
      (by
        intro A hA
        simp only [events, List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl | rfl
        · exact E.horizontalCrossingEvent_isIncreasing _ _ _ _
        · exact E.horizontalCrossingEvent_isIncreasing _ _ _ _
        · exact E.verticalCrossingEvent_isIncreasing _ _ _ _)
      (by
        intro A hA
        simp only [events, List.mem_cons, List.not_mem_nil, or_false] at hA
        rcases hA with rfl | rfl | rfl
        · exact hfirst
        · exact hsecond
        · exact hconnector)
  calc
    s ^ 3 = s ^ events.length := by simp [events]
    _ ≤ mu.real (finiteEventIntersection events) := hintersection
    _ ≤ mu.real (E.horizontalCrossingEvent a b c d) :=
      measureReal_mono (by
        simpa only [events] using
          E.finiteEventIntersection_overlapCrossings hBpos hB hal hmb
            hleft hright hheight)


theorem PeriodicPlaneEmbedding.iterated_overlapCrossings_measureReal_ge_pow
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V))) [IsProbabilityMeasure mu]
    (hFKG : IsFKG mu) (B a c d : Real)
    (left right : Nat -> Real) (n : Nat) (s : Real) (hs : 0 <= s)
    (hBpos : 0 < B)
    (hB : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2),
      |E.coordinates (E.edgeArc hxy t - E.vertex x) i| <= B)
    (hal : forall k, k < n -> a <= left k)
    (hmb : forall k, k < n -> right k <= right (k + 1))
    (hleft : forall k, k < n -> a + 5 * B < right k - 5 * B)
    (hright : forall k, k < n ->
      left k + 5 * B < right (k + 1) - 5 * B)
    (hheight : forall k, k < n ->
      c - 4 * B * ((k + 1 : Nat) : Real) + 5 * B <
        d + 4 * B * ((k + 1 : Nat) : Real) - 5 * B)
    (hinitial : s <= mu.real
      (E.horizontalCrossingEvent a (right 0) c d))
    (hhorizontal : forall k, k < n -> s <= mu.real
      (E.horizontalCrossingEvent (left k) (right (k + 1))
        (c - 4 * B * (k : Real)) (d + 4 * B * (k : Real))))
    (hvertical : forall k, k < n -> s <= mu.real
      (E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B)
        (c - 4 * B * ((k + 1 : Nat) : Real))
        (d + 4 * B * ((k + 1 : Nat) : Real)))) :
    s ^ (1 + 2 * n) <= mu.real
      (E.horizontalCrossingEvent a (right n)
        (c - 4 * B * (n : Real)) (d + 4 * B * (n : Real))) := by
  let lower : Nat -> Real := fun k => c - 4 * B * (k : Real)
  let upper : Nat -> Real := fun k => d + 4 * B * (k : Real)
  let target : Nat -> Set (ConfigSpace (Sym2 V)) := fun k =>
    E.horizontalCrossingEvent a (right k) (lower k) (upper k)
  let stepEvents : Nat -> List (Set (ConfigSpace (Sym2 V))) := fun k =>
    [E.horizontalCrossingEvent (left k) (right (k + 1))
        (lower k) (upper k),
     E.verticalCrossingEvent (left k + 4 * B) (right k - 4 * B)
        (lower (k + 1)) (upper (k + 1))]
  let events := target 0 :: (List.range n).flatMap stepEvents
  have hdeterministic : finiteEventIntersection events <= target n := by
    simpa only [events, target, stepEvents, lower, upper] using
      E.iterated_overlapCrossings_glue_horizontal B a c d left right n
        hBpos hB hal hmb hleft hright hheight
  have hmeasurable : forall A, A ∈ events -> MeasurableSet A := by
    intro A hA
    simp only [events, List.mem_cons, List.mem_flatMap, List.mem_range] at hA
    rcases hA with rfl | ⟨k, hk, hA⟩
    · exact E.horizontalCrossingEvent_measurableSet _ _ _ _
    · simp only [stepEvents, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact E.horizontalCrossingEvent_measurableSet _ _ _ _
      · exact E.verticalCrossingEvent_measurableSet _ _ _ _
  have hincreasing : forall A, A ∈ events -> IsIncreasing A := by
    intro A hA
    simp only [events, List.mem_cons, List.mem_flatMap, List.mem_range] at hA
    rcases hA with rfl | ⟨k, hk, hA⟩
    · exact E.horizontalCrossingEvent_isIncreasing _ _ _ _
    · simp only [stepEvents, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · exact E.horizontalCrossingEvent_isIncreasing _ _ _ _
      · exact E.verticalCrossingEvent_isIncreasing _ _ _ _
  have hlower : forall A, A ∈ events -> s <= mu.real A := by
    intro A hA
    simp only [events, List.mem_cons, List.mem_flatMap, List.mem_range] at hA
    rcases hA with rfl | ⟨k, hk, hA⟩
    · simpa only [target, lower, upper, Nat.cast_zero, mul_zero,
        sub_zero, add_zero] using hinitial
    · simp only [stepEvents, List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl
      · simpa only [lower, upper] using hhorizontal k hk
      · simpa only [lower, upper] using hvertical k hk
  have hintersection : s ^ events.length <=
      mu.real (finiteEventIntersection events) :=
    finiteEventIntersection_measureReal_ge_pow mu hFKG s hs events
      hmeasurable hincreasing hlower
  have hlength : events.length = 1 + 2 * n := by
    simp only [events, List.length_cons, List.length_flatMap, stepEvents,
      List.length_cons]
    simp
    omega
  calc
    s ^ (1 + 2 * n) = s ^ events.length := by rw [hlength]
    _ <= mu.real (finiteEventIntersection events) := hintersection
    _ <= mu.real (target n) := measureReal_mono hdeterministic
    _ = mu.real (E.horizontalCrossingEvent a (right n)
        (c - 4 * B * (n : Real)) (d + 4 * B * (n : Real))) := rfl


end StatMech.FK.PeriodicPlanar
