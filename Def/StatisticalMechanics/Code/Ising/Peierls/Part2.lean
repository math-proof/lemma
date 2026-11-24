module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Ising.Gibbs.Part6
public import Theorem.StatisticalMechanics.Code.Ising.InfiniteVolume.Part9
public import Theorem.StatisticalMechanics.Code.Ising.Peierls
open MeasureTheory Filter Topology Finset
open scoped BigOperators ENNReal
set_option linter.unusedVariables false
set_option linter.style.show false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/Peierls.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}


def flipInteriorEquiv {n : ℕ} :
    ({x // x ∈ box d n} → Bool) ≃ ({x // x ∈ box d n} → Bool) where
  toFun := flipInterior
  invFun := flipInterior
  left_inv := flipInterior_involutive
  right_inv := flipInterior_involutive

end Ising
end StatMech
