module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface.Part3
open Set SimpleGraph


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open Lattice


def boolTriangleTransitionCount (a b c : Bool) : Nat :=
  (if a = b then 0 else 1) + (if b = c then 0 else 1) +
    (if c = a then 0 else 1)


end StatMech.FK.PeriodicPlanar
