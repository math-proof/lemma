/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpbpivotbridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wcddefectbridge.Part5
import Theorem.StatisticalMechanics.Code.Walls.jc5_singlecycle.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedProof
import Theorem.StatisticalMechanics.Code.Walls.wpbpivotbridge.Part2
open scoped BigOperators
open Finset
open SimpleGraph Function


namespace StatMech

namespace Wpb

open StatMech.Lattice

open StatMech.Wad

open StatMech.Wcd

open StatMech.Walls

open StatMech.Euc


def WpbOrbitCovers (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) : Prop :=
  ∀ d : Dart, IsBoundaryDart K d → SameOrbit K a.1 d


end Wpb
end StatMech
