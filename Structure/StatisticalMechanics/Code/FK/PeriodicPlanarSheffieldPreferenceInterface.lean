/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPreferenceInterface.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectanglePreference.Part4
public import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
public import Abbrev.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface
public section

open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


structure PreferenceTriangle (n m : Nat) where
  col : Fin n
  row : Fin m
  upper : Bool
deriving DecidableEq, Fintype

end StatMech.FK.PeriodicPlanar
