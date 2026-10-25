/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wdcdartconnected.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.wotsorbitsurj.Part2
import Theorem.StatisticalMechanics.Code.Walls.wdcdartconnected.Part3
open SimpleGraph Function


namespace StatMech

namespace Wots

open StatMech.Lattice


def wdc_LayerConnected (K : Set (Site 2)) : Prop :=
  ∀ a b : {x : Site 2 // x ∈ wdc_boundaryLayer K},
    ((hypercubicLattice 2).induce (Kᶜ : Set (Site 2))).Reachable ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩ →
    (wdc_layerGraph K).Reachable a b


end Wots
end StatMech
