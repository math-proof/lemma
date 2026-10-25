/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonRectangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryEnlargement
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRectangleTranslation
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

def commonRectLeftShift (M : Nat → Nat) (N : Nat) : Site 2 :=
  fun i => if i = 0 then -(M N : Int) else 0

def commonRectRightShift (M : Nat → Nat) (N : Nat) : Site 2 :=
  fun i => if i = 0 then (M N : Int) else 0

def commonRectBottomShift (M : Nat → Nat) (N : Nat) : Site 2 :=
  fun i => if i = 1 then -(M N : Int) else 0

def commonRectTopShift (M : Nat → Nat) (N : Nat) : Site 2 :=
  fun i => if i = 1 then (M N : Int) else 0


end StatMech.FK.PeriodicPlanar
