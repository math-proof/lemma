module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldAdaptiveEndpoint.Part5
open Filter MeasureTheory Set Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldAdaptiveEndpoint.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V W : Type*} [DecidableEq V] [DecidableEq W]
  [Countable V] [Countable W]
  {P : PeriodicGraph V} {Pdual : PeriodicGraph W}


def opposedEndpointVerticalScore (width height : Nat) : Real :=
  if height < width then 1 else 0


def opposedEndpointHorizontalScore (width height : Nat) : Real :=
  if width < height then 1 else 0

end StatMech.FK.PeriodicPlanar
