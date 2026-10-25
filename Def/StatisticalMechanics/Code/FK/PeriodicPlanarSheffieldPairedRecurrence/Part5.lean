/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part13
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

def PeriodicPlaneEmbedding.CarriedCrossNestedArray.reframe
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (data : E.CarriedCrossNestedArray mu)
    (aWide bWide cTall dTall : Nat -> Real)
    (hwideLeft : forall n, aWide n <= data.a n)
    (hwideRight : forall n, data.b n <= bWide n)
    (htallBottom : forall n, cTall n <= data.c n)
    (htallTop : forall n, data.d n <= dTall n)
    (hverticalConnector : forall n,
      (P.orbitBox (P.bufferedRadius (data.verticalRadius n)) : Set V) <=
        E.rectVertices (aWide n) (bWide n) (data.c n) (data.d n))
    (hhorizontalConnector : forall n,
      (P.orbitBox (P.bufferedRadius (data.horizontalRadius n)) : Set V) <=
        E.rectVertices (data.a n) (data.b n) (cTall n) (dTall n)) :
    E.CarriedCrossNestedArray mu where
  a := data.a
  b := data.b
  c := data.c
  d := data.d
  aWide := aWide
  bWide := bWide
  cTall := cTall
  dTall := dTall
  bottom := data.bottom
  top := data.top
  left := data.left
  right := data.right
  verticalRadius := data.verticalRadius
  horizontalRadius := data.horizontalRadius
  wideLeft := hwideLeft
  wideRight := hwideRight
  tallBottom := htallBottom
  tallTop := htallTop
  verticalConnector := hverticalConnector
  horizontalConnector := hhorizontalConnector
  bottomLimit := data.bottomLimit
  topLimit := data.topLimit
  leftLimit := data.leftLimit
  rightLimit := data.rightLimit
  verticalMergeLimit := data.verticalMergeLimit
  horizontalMergeLimit := data.horizontalMergeLimit


noncomputable def PeriodicPlaneEmbedding.CarriedCrossNestedArray.reframeByCoordinateBounds
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (data : E.CarriedCrossNestedArray mu) :
    E.CarriedCrossNestedArray mu := by
  let xBound : Nat -> Real := fun n =>
    E.orbitBoxCoordinateBound
      (P.bufferedRadius (data.verticalRadius n)) 0
  let yBound : Nat -> Real := fun n =>
    E.orbitBoxCoordinateBound
      (P.bufferedRadius (data.horizontalRadius n)) 1
  apply data.reframe E mu
    (fun n => min (data.a n) (-xBound n))
    (fun n => max (data.b n) (xBound n))
    (fun n => min (data.c n) (-yBound n))
    (fun n => max (data.d n) (yBound n))
  · intro n
    exact min_le_left _ _
  · intro n
    exact le_max_left _ _
  · intro n
    exact min_le_left _ _
  · intro n
    exact le_max_left _ _
  · intro n v hv
    have hold := data.verticalConnector n hv
    have hx := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (0 : Fin 2)
    rw [abs_le] at hx
    exact ⟨(min_le_right (data.a n) (-xBound n)).trans hx.1,
      hx.2.trans (le_max_right (data.b n) (xBound n)),
      hold.2.2.1, hold.2.2.2⟩
  · intro n v hv
    have hold := data.horizontalConnector n hv
    have hy := E.abs_vertexCoord_le_orbitBoxCoordinateBound hv (1 : Fin 2)
    rw [abs_le] at hy
    exact ⟨hold.1, hold.2.1,
      (min_le_right (data.c n) (-yBound n)).trans hy.1,
      hy.2.trans (le_max_right (data.d n) (yBound n))⟩


end StatMech.FK.PeriodicPlanar
