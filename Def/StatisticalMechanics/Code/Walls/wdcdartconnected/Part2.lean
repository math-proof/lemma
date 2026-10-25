/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wotsorbitsurj.Part2
import Theorem.StatisticalMechanics.Code.Walls.wdcdartconnected
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice


def wdc_layerGraph (K : Set (Site 2)) : SimpleGraph {v : Site 2 // v ∈ wdc_boundaryLayer K} where
  Adj a b := KingAdj (a : Site 2) (b : Site 2) ∧
    ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable
      ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩
  symm := by
    constructor
    intro a b h
    exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun a h => h.1.1 rfl⟩

end Wots
end StatMech
