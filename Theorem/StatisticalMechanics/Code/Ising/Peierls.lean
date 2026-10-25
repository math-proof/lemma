/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
import Def.StatisticalMechanics.Code.Ising.Peierls
open MeasureTheory Filter Topology Finset
open scoped BigOperators ENNReal


set_option linter.unusedVariables false

set_option linter.style.show false


namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


@[simp] lemma flipConfig_apply (s : ConfigSpace (Site d)) (y : Site d) :
    flipConfig s y = !(s y) := rfl


@[simp] lemma flipConfig_involutive (s : ConfigSpace (Site d)) :
    flipConfig (flipConfig s) = s := by funext y; simp [flipConfig]


lemma flipInterior_involutive {n : ℕ} (τ : {x // x ∈ box d n} → Bool) :
    flipInterior (flipInterior τ) = τ := by funext x; simp [flipInterior]


end Ising
end StatMech
