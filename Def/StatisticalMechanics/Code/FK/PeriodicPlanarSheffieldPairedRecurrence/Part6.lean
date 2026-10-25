/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldVariablePadding.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part14
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}

def PeriodicPlaneEmbedding.CarriedCrossNestedArray.tail
    (E : PeriodicPlaneEmbedding P)
    (mu : Measure (ConfigSpace (Sym2 V)))
    (data : E.CarriedCrossNestedArray mu) :
    E.CarriedCrossNestedArray mu where
  a n := data.a (n + 1)
  b n := data.b (n + 1)
  c n := data.c (n + 1)
  d n := data.d (n + 1)
  aWide n := data.aWide (n + 1)
  bWide n := data.bWide (n + 1)
  cTall n := data.cTall (n + 1)
  dTall n := data.dTall (n + 1)
  bottom n := data.bottom (n + 1)
  top n := data.top (n + 1)
  left n := data.left (n + 1)
  right n := data.right (n + 1)
  verticalRadius n := data.verticalRadius (n + 1)
  horizontalRadius n := data.horizontalRadius (n + 1)
  wideLeft n := data.wideLeft (n + 1)
  wideRight n := data.wideRight (n + 1)
  tallBottom n := data.tallBottom (n + 1)
  tallTop n := data.tallTop (n + 1)
  verticalConnector n := data.verticalConnector (n + 1)
  horizontalConnector n := data.horizontalConnector (n + 1)
  bottomLimit := data.bottomLimit.comp (tendsto_add_atTop_nat 1)
  topLimit := data.topLimit.comp (tendsto_add_atTop_nat 1)
  leftLimit := data.leftLimit.comp (tendsto_add_atTop_nat 1)
  rightLimit := data.rightLimit.comp (tendsto_add_atTop_nat 1)
  verticalMergeLimit :=
    data.verticalMergeLimit.comp (tendsto_add_atTop_nat 1)
  horizontalMergeLimit :=
    data.horizontalMergeLimit.comp (tendsto_add_atTop_nat 1)


end StatMech.FK.PeriodicPlanar
