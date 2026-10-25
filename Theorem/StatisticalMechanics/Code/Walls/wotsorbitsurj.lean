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
import Def.StatisticalMechanics.Code.Walls.wotsorbitsurj
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice

open StatMech.Wpb

open StatMech.Wcd

open StatMech.Euc


theorem wots_dartGraph_adj (K : Set (Site 2)) (d1 d2 : {e : Dart // IsBoundaryDart K e}) :
    (wots_dartGraph K).Adj d1 d2 ↔
      d1 ≠ d2 ∧
      (KingAdj d1.1.head d2.1.head ∨ d1.1.head = d2.1.head) ∧
      ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
        ⟨d1.1.head, d1.2.2⟩ ⟨d2.1.head, d2.2.2⟩ := Iff.rfl


end Wots
end StatMech
