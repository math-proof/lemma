/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Ising.Gibbs
open scoped BigOperators
open Finset


namespace StatMech

namespace Ising

section Spins

variable {V : Type*}


def bond (s : ConfigSpace V) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y => spin s x * spin s y, fun _ _ => mul_comm _ _⟩ e

end Spins
end Ising
end StatMech
