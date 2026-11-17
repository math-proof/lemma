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
public import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPreferenceInterface
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open Lattice


public inductive PreferenceInterfaceNode (n m : Nat)
  | left
  | right
  | bottom
  | top
  | triangle (t : PreferenceTriangle n m)
deriving DecidableEq, Fintype

end StatMech.FK.PeriodicPlanar
