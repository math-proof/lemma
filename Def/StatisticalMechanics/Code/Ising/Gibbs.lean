/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section Spins

variable {V : Type*}


def spin (s : ConfigSpace V) (x : V) : ℝ := if s x then 1 else -1

end Spins
end Ising
end StatMech
