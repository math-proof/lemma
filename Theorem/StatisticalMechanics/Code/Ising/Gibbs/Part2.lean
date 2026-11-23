/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Gibbs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib
public import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
public import Def.StatisticalMechanics.Code.Ising.Gibbs.Part2
open scoped BigOperators
open Finset

public section

namespace StatMech

namespace Ising

section Spins

variable {V : Type*}


@[simp] lemma bond_mk (s : ConfigSpace V) (x y : V) :
    bond s s(x, y) = spin s x * spin s y := rfl

end Spins
end Ising
end StatMech
