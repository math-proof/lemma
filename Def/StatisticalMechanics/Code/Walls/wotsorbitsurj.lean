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
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice

open StatMech.Wpb

open StatMech.Wcd

open StatMech.Euc


def wots_dartGraph (K : Set (Site 2)) : SimpleGraph {e : Dart // IsBoundaryDart K e} where
  Adj d1 d2 := d1 ≠ d2 ∧
    (KingAdj d1.1.head d2.1.head ∨ d1.1.head = d2.1.head) ∧
    ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
      ⟨d1.1.head, d1.2.2⟩ ⟨d2.1.head, d2.2.2⟩
  symm := by
    constructor
    intro a b h
    refine ⟨h.1.symm, ?_, h.2.2.symm⟩
    rcases h.2.1 with hk | he
    · exact Or.inl hk.symm
    · exact Or.inr he.symm
  loopless := ⟨fun _ h => h.1 rfl⟩

end Wots
end StatMech
