/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Ising.Gibbs
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section Spins

variable {V : Type*}


@[simp] lemma spin_true (s : ConfigSpace V) {x : V} (hx : s x = true) : spin s x = 1 := by
  simp [spin, hx]

@[simp] lemma spin_false (s : ConfigSpace V) {x : V} (hx : s x = false) : spin s x = -1 := by
  simp [spin, hx]


lemma spin_sq (s : ConfigSpace V) (x : V) : spin s x * spin s x = 1 := by
  unfold spin; by_cases hx : s x <;> simp [hx]


lemma abs_spin_le_one (s : ConfigSpace V) (x : V) : |spin s x| ≤ 1 := by
  unfold spin; by_cases hx : s x <;> simp [hx]


end Spins
end Ising
end StatMech
