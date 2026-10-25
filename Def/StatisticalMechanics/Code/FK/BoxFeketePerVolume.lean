/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxFeketePerVolume.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Theorem.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part6
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {d : ℕ}


def bpv_PerVolumeFreeEnergyData (d : ℕ) (t : ℝ) : Prop :=
  ∃ (δ osc : ℕ → ℝ),
    (∀ j, 0 ≤ δ j)
    ∧ Summable δ
    ∧ (∀ j, ivp2_tiltFreeEnergy (boxGraph d (2 ^ j)) 2 t - δ j
        ≤ ivp2_tiltFreeEnergy (boxGraph d (2 ^ (j + 1))) 2 t)
    ∧ BddAbove (range (fun j => ivp2_tiltFreeEnergy (boxGraph d (2 ^ j)) 2 t))
    ∧ Tendsto osc atTop (𝓝 0)
    ∧ (∀ n, 1 ≤ n → |ivp2_tiltFreeEnergy (boxGraph d n) 2 t
        - ivp2_tiltFreeEnergy (boxGraph d (2 ^ (Nat.log 2 n))) 2 t| ≤ osc (Nat.log 2 n))


end FK
end StatMech
