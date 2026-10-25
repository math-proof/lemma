/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wotsorbitsurj.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnectedGlobal.Part2
import Theorem.StatisticalMechanics.Code.Lattice.KingFacts
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Walls.wifinterfaceconn
import Theorem.StatisticalMechanics.Code.Walls.wotsorbitsurj
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice

open StatMech.Wpb

open StatMech.Wcd

open StatMech.Euc


def wots_LocalStepSameOrbit (K : Set (Site 2)) : Prop :=
  ∀ d1 d2 : {e : Dart // IsBoundaryDart K e},
    (wots_dartGraph K).Adj d1 d2 → SameOrbit K d1.1 d2.1


def wots_DartConnected (K : Set (Site 2)) : Prop :=
  ∀ d1 d2 : {e : Dart // IsBoundaryDart K e},
    ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
      ⟨d1.1.head, d1.2.2⟩ ⟨d2.1.head, d2.2.2⟩ →
    (wots_dartGraph K).Reachable d1 d2


end Wots
end StatMech
