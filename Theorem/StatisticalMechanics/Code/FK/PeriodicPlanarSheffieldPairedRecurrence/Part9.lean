/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part4
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

namespace AlignedCrossNestedPairedSequence

theorem primalAdjacent_transitionCoordinates
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hlimit : Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent 0
        (data.triple n).currentX 0 (data.triple n).currentY))
      (mu.real (E.verticalCrossingEvent
        (data.triple n).current.raw.data.wideLeft
        (data.triple n).current.raw.data.wideRight 0
        (data.triple n).currentY))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (data.transitionA0 n) (data.transitionB0 n)
        (data.transitionC0 n + padding)
        (data.transitionD0 n - padding)))
      (mu.real (E.verticalCrossingEvent
        (data.transitionA1 n + padding)
        (data.transitionB1 n - padding)
        (data.transitionC1 n) (data.transitionD1 n))))
      atTop (nhds 1) := by
  simpa [transitionA0, transitionB0, transitionC0, transitionD0,
    transitionA1, transitionB1, transitionC1, transitionD1] using hlimit


theorem primalAdjacent_translatedTransitionCoordinates
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hTI : P.IsTranslationInvariant mu) (z0 z1 : Nat -> Site 2)
    (hlimit : Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent 0
        (data.triple n).currentX 0 (data.triple n).currentY))
      (mu.real (E.verticalCrossingEvent
        (data.triple n).current.raw.data.wideLeft
        (data.triple n).current.raw.data.wideRight 0
        (data.triple n).currentY))) atTop (nhds 1)) :
    Tendsto (fun n => max
      (mu.real (E.horizontalCrossingEvent
        (data.transitionA0 n + z0 n 0)
        (data.transitionB0 n + z0 n 0)
        (data.transitionC0 n + padding + z0 n 1)
        (data.transitionD0 n - padding + z0 n 1)))
      (mu.real (E.verticalCrossingEvent
        (data.transitionA1 n + padding + z1 n 0)
        (data.transitionB1 n - padding + z1 n 0)
        (data.transitionC1 n + z1 n 1)
        (data.transitionD1 n + z1 n 1)))) atTop (nhds 1) := by
  have hbase := data.primalAdjacent_transitionCoordinates hlimit
  simpa only [Int.cast_ofNat, add_assoc] using
    E.crossingMax_independent_translate_tendsto_one mu hTI z0 z1
      data.transitionA0 data.transitionB0
      (fun n => data.transitionC0 n + padding)
      (fun n => data.transitionD0 n - padding)
      (fun n => data.transitionA1 n + padding)
      (fun n => data.transitionB1 n - padding)
      data.transitionC1 data.transitionD1 hbase


theorem endpoint_transitionCoordinates_of_mergeLimits
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1)
    (hmergeVertical : Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        (data.triple n).previous.raw.data.primalBottomSource
        (data.triple n).previous.raw.data.primalTopSource))
      atTop (nhds 0))
    (hmergeHorizontal : Tendsto (fun n => mu.real
      (E.rectanglePairMergeErrorUnion 0
        (data.triple n).nextX 0 (data.triple n).nextY
        (data.triple n).next.raw.data.primalLeftSource
        (data.triple n).next.raw.data.primalRightSource))
      atTop (nhds 0)) :
    Tendsto (fun n => mu.real (E.verticalCrossingEvent
      (data.transitionA0 n + padding)
      (data.transitionB0 n - padding)
      (data.transitionC0 n) (data.transitionD0 n)))
      atTop (nhds 1) /\
    Tendsto (fun n => mu.real (E.horizontalCrossingEvent
      (data.transitionA1 n) (data.transitionB1 n)
      (data.transitionC1 n + padding)
      (data.transitionD1 n - padding))) atTop (nhds 1) := by
  have hbottom : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        ((data.triple n).previous.raw.data.primalBottomSource : Set V)
        (E.rectBottomBoundaryVertices
          (data.triple n).previous.raw.data.wideLeft
          (data.triple n).previous.raw.data.wideRight 0
          (data.triple n).previousY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).previous.raw.shortTop_eq] using
          le_of_lt (data.triple n).previous.raw.data.primalBottomScore)
      (fun _ => measureReal_le_one)
  have htop : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        ((data.triple n).previous.raw.data.primalTopSource : Set V)
        (E.rectTopBoundaryVertices
          (data.triple n).previous.raw.data.wideLeft
          (data.triple n).previous.raw.data.wideRight 0
          (data.triple n).previousY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).previous.raw.shortTop_eq] using
          le_of_lt (data.triple n).previous.raw.data.primalTopScore)
      (fun _ => measureReal_le_one)
  have hleft : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent 0 (data.triple n).nextX 0
        (data.triple n).nextY
        ((data.triple n).next.raw.data.primalLeftSource : Set V)
        (E.rectLeftBoundaryVertices 0 (data.triple n).nextX 0
          (data.triple n).nextY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).next.raw.narrowRight_eq,
          (data.triple n).next.raw.tallTop_eq] using
          le_of_lt (data.triple n).next.raw.data.primalLeftScore)
      (fun _ => measureReal_le_one)
  have hright : Tendsto (fun n => mu.real
      (E.rectSideConnectionEvent 0 (data.triple n).nextX 0
        (data.triple n).nextY
        ((data.triple n).next.raw.data.primalRightSource : Set V)
        (E.rectRightBoundaryVertices 0 (data.triple n).nextX 0
          (data.triple n).nextY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).next.raw.narrowRight_eq,
          (data.triple n).next.raw.tallTop_eq] using
          le_of_lt (data.triple n).next.raw.data.primalRightScore)
      (fun _ => measureReal_le_one)
  have hvertical := E.verticalCrossing_tendsto_one_of_boundaryScores
    mu hFKG
    (fun n => (data.triple n).previous.raw.data.wideLeft)
    (fun n => (data.triple n).previous.raw.data.wideRight)
    (fun _ => 0) (fun n => (data.triple n).previousY)
    (fun n => (data.triple n).previous.raw.data.primalBottomSource)
    (fun n => (data.triple n).previous.raw.data.primalTopSource)
    hbottom htop hmergeVertical
  have hhorizontal := E.horizontalCrossing_tendsto_one_of_boundaryScores
    mu hFKG (fun _ => 0) (fun n => (data.triple n).nextX)
    (fun _ => 0) (fun n => (data.triple n).nextY)
    (fun n => (data.triple n).next.raw.data.primalLeftSource)
    (fun n => (data.triple n).next.raw.data.primalRightSource)
    hleft hright hmergeHorizontal
  let zVertical : Nat -> Site 2 := fun n => fun i =>
    if i = 0 then padding -
      (data.triple n).previous.raw.wideLeftInt else -(padding : Int)
  let zHorizontal : Nat -> Site 2 := fun n => fun i =>
    if i = 0 then
      (data.triple n).current.raw.wideLeftInt - padding
    else padding
  constructor
  · have htranslated := E.verticalCrossing_translate_tendsto_one
      mu hTI zVertical
      (fun n => (data.triple n).previous.raw.data.wideLeft)
      (fun n => (data.triple n).previous.raw.data.wideRight)
      (fun _ => 0) (fun n => (data.triple n).previousY) hvertical
    apply htranslated.congr'
    filter_upwards with n
    have hcurrentR : ((data.triple n).currentX : Real) =
        ((data.triple n).previous.raw.wideRightInt : Real) -
          (data.triple n).previous.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).currentX_eq
    have hpreviousYR : ((data.triple n).previousY : Real) =
        (data.triple n).currentY + 2 * padding := by
      exact_mod_cast (data.triple n).previousY_eq
    apply congrArg (fun event : Set (ConfigSpace (Sym2 V)) => mu.real event)
    congr 1
    all_goals
      simp only [transitionA0, transitionB0, transitionC0, transitionD0,
        zVertical, Pi.zero_apply, if_pos, if_neg]
    · rw [(data.triple n).previous.raw.wideLeft_eq]
      push_cast
      ring
    · rw [(data.triple n).previous.raw.wideRight_eq]
      push_cast
      linarith [hcurrentR]
    · push_cast
      ring
    · push_cast
      linarith [hpreviousYR]
  · have htranslated := E.horizontalCrossing_translate_tendsto_one
      mu hTI zHorizontal (fun _ => 0)
      (fun n => (data.triple n).nextX) (fun _ => 0)
      (fun n => (data.triple n).nextY) hhorizontal
    apply htranslated.congr'
    filter_upwards with n
    have hnextR : ((data.triple n).nextX : Real) =
        ((data.triple n).current.raw.wideRightInt : Real) -
          (data.triple n).current.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).nextX_eq
    have hcurrentYR : ((data.triple n).currentY : Real) =
        (data.triple n).nextY + 2 * padding := by
      exact_mod_cast (data.triple n).currentY_eq
    apply congrArg (fun event : Set (ConfigSpace (Sym2 V)) => mu.real event)
    congr 1
    all_goals
      simp only [transitionA1, transitionB1, transitionC1, transitionD1,
        zHorizontal, Pi.zero_apply, if_pos, if_neg]
    · rw [(data.triple n).current.raw.wideLeft_eq]
      push_cast
      ring
    · rw [(data.triple n).current.raw.wideRight_eq]
      push_cast
      linarith [hnextR]
    · push_cast
      linarith [hcurrentYR]


theorem dual_endpoint_transitionCoordinates_of_mergeLimits
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hFKG : IsFKG muDual) (hTI : Pdual.IsTranslationInvariant muDual)
    (hp : Tendsto pDual atTop (nhds 1))
    (hp_le : forall n, pDual n <= 1)
    (hmergeVertical : Tendsto (fun n => muDual.real
      (Edual.rectanglePairMergeErrorUnion
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        (data.triple n).previous.raw.data.dualBottomSource
        (data.triple n).previous.raw.data.dualTopSource))
      atTop (nhds 0))
    (hmergeHorizontal : Tendsto (fun n => muDual.real
      (Edual.rectanglePairMergeErrorUnion 0
        (data.triple n).nextX 0 (data.triple n).nextY
        (data.triple n).next.raw.data.dualLeftSource
        (data.triple n).next.raw.data.dualRightSource))
      atTop (nhds 0)) :
    Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
      (data.transitionA0 n + padding)
      (data.transitionB0 n - padding)
      (data.transitionC0 n) (data.transitionD0 n)))
      atTop (nhds 1) /\
    Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
      (data.transitionA1 n) (data.transitionB1 n)
      (data.transitionC1 n + padding)
      (data.transitionD1 n - padding))) atTop (nhds 1) := by
  have hbottom : Tendsto (fun n => muDual.real
      (Edual.rectSideConnectionEvent
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        ((data.triple n).previous.raw.data.dualBottomSource : Set W)
        (Edual.rectBottomBoundaryVertices
          (data.triple n).previous.raw.data.wideLeft
          (data.triple n).previous.raw.data.wideRight 0
          (data.triple n).previousY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).previous.raw.shortTop_eq] using
          le_of_lt (data.triple n).previous.raw.data.dualBottomScore)
      (fun _ => measureReal_le_one)
  have htop : Tendsto (fun n => muDual.real
      (Edual.rectSideConnectionEvent
        (data.triple n).previous.raw.data.wideLeft
        (data.triple n).previous.raw.data.wideRight 0
        (data.triple n).previousY
        ((data.triple n).previous.raw.data.dualTopSource : Set W)
        (Edual.rectTopBoundaryVertices
          (data.triple n).previous.raw.data.wideLeft
          (data.triple n).previous.raw.data.wideRight 0
          (data.triple n).previousY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).previous.raw.shortTop_eq] using
          le_of_lt (data.triple n).previous.raw.data.dualTopScore)
      (fun _ => measureReal_le_one)
  have hleft : Tendsto (fun n => muDual.real
      (Edual.rectSideConnectionEvent 0 (data.triple n).nextX 0
        (data.triple n).nextY
        ((data.triple n).next.raw.data.dualLeftSource : Set W)
        (Edual.rectLeftBoundaryVertices 0 (data.triple n).nextX 0
          (data.triple n).nextY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).next.raw.narrowRight_eq,
          (data.triple n).next.raw.tallTop_eq] using
          le_of_lt (data.triple n).next.raw.data.dualLeftScore)
      (fun _ => measureReal_le_one)
  have hright : Tendsto (fun n => muDual.real
      (Edual.rectSideConnectionEvent 0 (data.triple n).nextX 0
        (data.triple n).nextY
        ((data.triple n).next.raw.data.dualRightSource : Set W)
        (Edual.rectRightBoundaryVertices 0 (data.triple n).nextX 0
          (data.triple n).nextY))) atTop (nhds 1) := by
    exact hp.squeeze tendsto_const_nhds
      (fun n => by
        simpa [(data.triple n).next.raw.narrowRight_eq,
          (data.triple n).next.raw.tallTop_eq] using
          le_of_lt (data.triple n).next.raw.data.dualRightScore)
      (fun _ => measureReal_le_one)
  have hvertical := Edual.verticalCrossing_tendsto_one_of_boundaryScores
    muDual hFKG
    (fun n => (data.triple n).previous.raw.data.wideLeft)
    (fun n => (data.triple n).previous.raw.data.wideRight)
    (fun _ => 0) (fun n => (data.triple n).previousY)
    (fun n => (data.triple n).previous.raw.data.dualBottomSource)
    (fun n => (data.triple n).previous.raw.data.dualTopSource)
    hbottom htop hmergeVertical
  have hhorizontal := Edual.horizontalCrossing_tendsto_one_of_boundaryScores
    muDual hFKG (fun _ => 0) (fun n => (data.triple n).nextX)
    (fun _ => 0) (fun n => (data.triple n).nextY)
    (fun n => (data.triple n).next.raw.data.dualLeftSource)
    (fun n => (data.triple n).next.raw.data.dualRightSource)
    hleft hright hmergeHorizontal
  let zVertical : Nat -> Site 2 := fun n => fun i =>
    if i = 0 then padding -
      (data.triple n).previous.raw.wideLeftInt else -(padding : Int)
  let zHorizontal : Nat -> Site 2 := fun n => fun i =>
    if i = 0 then
      (data.triple n).current.raw.wideLeftInt - padding
    else padding
  constructor
  · have htranslated := Edual.verticalCrossing_translate_tendsto_one
      muDual hTI zVertical
      (fun n => (data.triple n).previous.raw.data.wideLeft)
      (fun n => (data.triple n).previous.raw.data.wideRight)
      (fun _ => 0) (fun n => (data.triple n).previousY) hvertical
    apply htranslated.congr'
    filter_upwards with n
    have hcurrentR : ((data.triple n).currentX : Real) =
        ((data.triple n).previous.raw.wideRightInt : Real) -
          (data.triple n).previous.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).currentX_eq
    have hpreviousYR : ((data.triple n).previousY : Real) =
        (data.triple n).currentY + 2 * padding := by
      exact_mod_cast (data.triple n).previousY_eq
    apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
      muDual.real event)
    congr 1
    all_goals
      simp only [transitionA0, transitionB0, transitionC0, transitionD0,
        zVertical, Pi.zero_apply, if_pos, if_neg]
    · rw [(data.triple n).previous.raw.wideLeft_eq]
      push_cast
      ring
    · rw [(data.triple n).previous.raw.wideRight_eq]
      push_cast
      linarith [hcurrentR]
    · push_cast
      ring
    · push_cast
      linarith [hpreviousYR]
  · have htranslated := Edual.horizontalCrossing_translate_tendsto_one
      muDual hTI zHorizontal (fun _ => 0)
      (fun n => (data.triple n).nextX) (fun _ => 0)
      (fun n => (data.triple n).nextY) hhorizontal
    apply htranslated.congr'
    filter_upwards with n
    have hnextR : ((data.triple n).nextX : Real) =
        ((data.triple n).current.raw.wideRightInt : Real) -
          (data.triple n).current.raw.wideLeftInt + 2 * padding := by
      exact_mod_cast (data.triple n).nextX_eq
    have hcurrentYR : ((data.triple n).currentY : Real) =
        (data.triple n).nextY + 2 * padding := by
      exact_mod_cast (data.triple n).currentY_eq
    apply congrArg (fun event : Set (ConfigSpace (Sym2 W)) =>
      muDual.real event)
    congr 1
    all_goals
      simp only [transitionA1, transitionB1, transitionC1, transitionD1,
        zHorizontal, Pi.zero_apply, if_pos, if_neg]
    · rw [(data.triple n).current.raw.wideLeft_eq]
      push_cast
      ring
    · rw [(data.triple n).current.raw.wideRight_eq]
      push_cast
      linarith [hnextR]
    · push_cast
      linarith [hcurrentYR]


theorem exists_endpoint_transitionCoordinates_of_connectorContainment
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))} [IsProbabilityMeasure mu]
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hFKG : IsFKG mu) (hTI : P.IsTranslationInvariant mu)
    (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
    (hp : Tendsto p atTop (nhds 1)) (hp_le : forall n, p n <= 1) :
    exists verticalRadius horizontalRadius : Nat -> Nat,
      (forall n, n <= verticalRadius n) /\
      (forall n, n <= horizontalRadius n) /\
      ((forall n,
        (P.orbitBox (P.bufferedRadius (verticalRadius n)) : Set V) <=
          E.rectVertices
            (data.triple n).previous.raw.data.wideLeft
            (data.triple n).previous.raw.data.wideRight 0
            (data.triple n).previousY) ->
       (forall n,
        (P.orbitBox (P.bufferedRadius (horizontalRadius n)) : Set V) <=
          E.rectVertices 0 (data.triple n).nextX 0
            (data.triple n).nextY) ->
       Tendsto (fun n => mu.real (E.verticalCrossingEvent
          (data.transitionA0 n + padding)
          (data.transitionB0 n - padding)
          (data.transitionC0 n) (data.transitionD0 n)))
          atTop (nhds 1) /\
       Tendsto (fun n => mu.real (E.horizontalCrossingEvent
          (data.transitionA1 n) (data.transitionB1 n)
          (data.transitionC1 n + padding)
          (data.transitionD1 n - padding))) atTop (nhds 1)) := by
  let bottom : Nat -> Finset V := fun n =>
    (data.triple n).previous.raw.data.primalBottomSource
  let top : Nat -> Fin 1 -> Finset V := fun n _ =>
    (data.triple n).previous.raw.data.primalTopSource
  let left : Nat -> Finset V := fun n =>
    (data.triple n).next.raw.data.primalLeftSource
  let right : Nat -> Fin 1 -> Finset V := fun n _ =>
    (data.triple n).next.raw.data.primalRightSource
  obtain ⟨verticalRadius, hverticalRadius, hverticalMerge⟩ :=
    E.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      mu hTI hunique bottom top
  obtain ⟨horizontalRadius, hhorizontalRadius, hhorizontalMerge⟩ :=
    E.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      mu hTI hunique left right
  refine ⟨verticalRadius, horizontalRadius, hverticalRadius,
    hhorizontalRadius, ?_⟩
  intro hverticalBox hhorizontalBox
  let z : Nat -> Site 2 := fun _ => 0
  let i : Nat -> Fin 1 := fun _ => 0
  have hshiftImage (s : Finset V) :
      s.image (P.shift (0 : Site 2)) = s := by
    ext v
    simp [P.shift_zero]
  have hmergeVertical := hverticalMerge z i
    (fun n => (data.triple n).previous.raw.data.wideLeft)
    (fun n => (data.triple n).previous.raw.data.wideRight)
    (fun _ => 0) (fun n => (data.triple n).previousY) (by
      intro n
      rw [show z n = 0 by rfl, P.shift_zero]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact hverticalBox n hu)
  have hmergeHorizontal := hhorizontalMerge z i
    (fun _ => 0) (fun n => (data.triple n).nextX)
    (fun _ => 0) (fun n => (data.triple n).nextY) (by
      intro n
      rw [show z n = 0 by rfl, P.shift_zero]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact hhorizontalBox n hu)
  apply data.endpoint_transitionCoordinates_of_mergeLimits
    hFKG hTI hp hp_le
  · simpa only [bottom, top, z, i, hshiftImage] using hmergeVertical
  · simpa only [left, right, z, i, hshiftImage] using hmergeHorizontal


theorem exists_dual_endpoint_transitionCoordinates_of_connectorContainment
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
      [IsProbabilityMeasure muDual]
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (hFKG : IsFKG muDual) (hTI : Pdual.IsTranslationInvariant muDual)
    (hunique : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
    (hp : Tendsto pDual atTop (nhds 1))
    (hp_le : forall n, pDual n <= 1) :
    exists verticalRadius horizontalRadius : Nat -> Nat,
      (forall n, n <= verticalRadius n) /\
      (forall n, n <= horizontalRadius n) /\
      ((forall n,
        (Pdual.orbitBox (Pdual.bufferedRadius (verticalRadius n)) : Set W) <=
          Edual.rectVertices
            (data.triple n).previous.raw.data.wideLeft
            (data.triple n).previous.raw.data.wideRight 0
            (data.triple n).previousY) ->
       (forall n,
        (Pdual.orbitBox
          (Pdual.bufferedRadius (horizontalRadius n)) : Set W) <=
          Edual.rectVertices 0 (data.triple n).nextX 0
            (data.triple n).nextY) ->
       Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent
          (data.transitionA0 n + padding)
          (data.transitionB0 n - padding)
          (data.transitionC0 n) (data.transitionD0 n)))
          atTop (nhds 1) /\
       Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent
          (data.transitionA1 n) (data.transitionB1 n)
          (data.transitionC1 n + padding)
          (data.transitionD1 n - padding))) atTop (nhds 1)) := by
  let bottom : Nat -> Finset W := fun n =>
    (data.triple n).previous.raw.data.dualBottomSource
  let top : Nat -> Fin 1 -> Finset W := fun n _ =>
    (data.triple n).previous.raw.data.dualTopSource
  let left : Nat -> Finset W := fun n =>
    (data.triple n).next.raw.data.dualLeftSource
  let right : Nat -> Fin 1 -> Finset W := fun n _ =>
    (data.triple n).next.raw.data.dualRightSource
  obtain ⟨verticalRadius, hverticalRadius, hverticalMerge⟩ :=
    Edual.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      muDual hTI hunique bottom top
  obtain ⟨horizontalRadius, hhorizontalRadius, hhorizontalMerge⟩ :=
    Edual.exists_uniform_translatedTemplate_mergeError_tendsto_zero
      muDual hTI hunique left right
  refine ⟨verticalRadius, horizontalRadius, hverticalRadius,
    hhorizontalRadius, ?_⟩
  intro hverticalBox hhorizontalBox
  let z : Nat -> Site 2 := fun _ => 0
  let i : Nat -> Fin 1 := fun _ => 0
  have hshiftImage (s : Finset W) :
      s.image (Pdual.shift (0 : Site 2)) = s := by
    ext v
    simp [Pdual.shift_zero]
  have hmergeVertical := hverticalMerge z i
    (fun n => (data.triple n).previous.raw.data.wideLeft)
    (fun n => (data.triple n).previous.raw.data.wideRight)
    (fun _ => 0) (fun n => (data.triple n).previousY) (by
      intro n
      rw [show z n = 0 by rfl, Pdual.shift_zero]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact hverticalBox n hu)
  have hmergeHorizontal := hhorizontalMerge z i
    (fun _ => 0) (fun n => (data.triple n).nextX)
    (fun _ => 0) (fun n => (data.triple n).nextY) (by
      intro n
      rw [show z n = 0 by rfl, Pdual.shift_zero]
      intro v hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact hhorizontalBox n hu)
  apply data.dual_endpoint_transitionCoordinates_of_mergeLimits
    hFKG hTI hp hp_le
  · simpa only [bottom, top, z, i, hshiftImage] using hmergeVertical
  · simpa only [left, right, z, i, hshiftImage] using hmergeHorizontal


theorem transitionCoordinates_spans
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (B : Nat) (hpadding : 5 * B < padding) :
    (forall n, data.transitionA0 n + 5 * B <
      data.transitionB0 n - 5 * B) /\
    (forall n, data.transitionC0 n + 5 * B <
      data.transitionD0 n - 5 * B) /\
    (forall n, data.transitionA1 n + 5 * B <
      data.transitionB1 n - 5 * B) /\
    (forall n, data.transitionC1 n + 5 * B <
      data.transitionD1 n - 5 * B) := by
  have hpadR : (5 * B : Real) < padding := by exact_mod_cast hpadding
  constructor
  · intro n
    have hspan := (data.triple n).previous.raw.extentX_le_wideSpan
    have hcurrent := (data.triple n).currentX_eq
    have hnonneg : (0 : Int) <=
        (data.triple n).previous.raw.wideRightInt -
          (data.triple n).previous.raw.wideLeftInt := by
      exact (show (0 : Int) <= (data.triple n).previousX by omega).trans hspan
    have hsize : (10 * B : Nat) < (data.triple n).currentX := by
      have hcast : (2 * padding : Int) <= (data.triple n).currentX := by
        rw [hcurrent]
        omega
      have hnat : 2 * padding <= (data.triple n).currentX := by
        exact_mod_cast hcast
      omega
    change (0 : Real) + 5 * (B : Real) <
      ((data.triple n).currentX : Real) - 5 * (B : Real)
    have hsizeR : (10 * B : Real) < (data.triple n).currentX := by
      exact_mod_cast hsize
    linarith
  · constructor
    · intro n
      have hsize : (10 * B : Nat) < (data.triple n).currentY := by
        rw [(data.triple n).currentY_eq]
        omega
      simp only [transitionC0, transitionD0]
      have hsizeR : (10 * B : Real) < (data.triple n).currentY := by
        exact_mod_cast hsize
      linarith
    · constructor
      · intro n
        have hleft := (data.triple n).current.raw.data.wideLeft_le
        have hright := (data.triple n).current.raw.data.narrowRight_le
        have hzeroRight : (0 : Real) <=
            (data.triple n).current.raw.data.wideRight := by
          exact (show (0 : Real) <= (data.triple n).currentX by positivity).trans
            (by simpa [(data.triple n).current.raw.narrowRight_eq] using hright)
        simp only [transitionA1, transitionB1]
        linarith
      · intro n
        have hsize : (10 * B : Nat) < (data.triple n).currentY := by
          rw [(data.triple n).currentY_eq]
          omega
        change (0 : Real) + 5 * (B : Real) <
          ((data.triple n).currentY : Real) - 5 * (B : Real)
        have hsizeR : (10 * B : Real) < (data.triple n).currentY := by
          exact_mod_cast hsize
        linarith


theorem transitionCoordinates_spans_of_current_gt
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (B : Real)
    (hcurrentX : forall n, 10 * B < (data.triple n).currentX)
    (hcurrentY : forall n, 10 * B < (data.triple n).currentY) :
    (forall n, data.transitionA0 n + 5 * B <
      data.transitionB0 n - 5 * B) /\
    (forall n, data.transitionC0 n + 5 * B <
      data.transitionD0 n - 5 * B) /\
    (forall n, data.transitionA1 n + 5 * B <
      data.transitionB1 n - 5 * B) /\
    (forall n, data.transitionC1 n + 5 * B <
      data.transitionD1 n - 5 * B) := by
  constructor
  · intro n
    simp only [transitionA0, transitionB0]
    linarith [hcurrentX n]
  constructor
  · intro n
    simp only [transitionC0, transitionD0]
    have hpad : (0 : Real) <= padding := by positivity
    linarith [hcurrentY n]
  constructor
  · intro n
    have hspan := (data.triple n).current.raw.extentX_le_wideSpan
    have hspanR : ((data.triple n).currentX : Real) <=
        (data.triple n).current.raw.wideRightInt -
          (data.triple n).current.raw.wideLeftInt := by
      exact_mod_cast hspan
    simp only [transitionA1, transitionB1]
    rw [(data.triple n).current.raw.wideLeft_eq,
      (data.triple n).current.raw.wideRight_eq]
    push_cast
    have hpad : (0 : Real) <= padding := by positivity
    linarith [hcurrentX n]
  · intro n
    simp only [transitionC1, transitionD1]
    linarith [hcurrentY n]


theorem translatedTransitionCoordinates_spans
    {E : PeriodicPlaneEmbedding P} {Edual : PeriodicPlaneEmbedding Pdual}
    {mu : Measure (ConfigSpace (Sym2 V))}
    {muDual : Measure (ConfigSpace (Sym2 W))}
    {p pDual : Nat -> Real}
    {family : forall n,
      E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
    {familyDual : forall n,
      Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
    {padding : Nat}
    (data : AlignedCrossNestedPairedSequence E Edual mu muDual
      p pDual family familyDual padding)
    (B : Nat) (hpadding : 5 * B < padding) (z0 z1 : Nat -> Site 2) :
    (forall n, data.transitionA0 n + z0 n 0 + 5 * B <
      data.transitionB0 n + z0 n 0 - 5 * B) /\
    (forall n, data.transitionC0 n + z0 n 1 + 5 * B <
      data.transitionD0 n + z0 n 1 - 5 * B) /\
    (forall n, data.transitionA1 n + z1 n 0 + 5 * B <
      data.transitionB1 n + z1 n 0 - 5 * B) /\
    (forall n, data.transitionC1 n + z1 n 1 + 5 * B <
      data.transitionD1 n + z1 n 1 - 5 * B) := by
  obtain ⟨hx0, hy0, hx1, hy1⟩ :=
    data.transitionCoordinates_spans B hpadding
  exact ⟨fun n => by linarith [hx0 n], fun n => by linarith [hy0 n],
    fun n => by linarith [hx1 n], fun n => by linarith [hy1 n]⟩

end AlignedCrossNestedPairedSequence
end StatMech.FK.PeriodicPlanar
