module
public import Theorem.StatisticalMechanics.Code.Exact3D.Ising3D.Part3
public import Theorem.StatisticalMechanics.Code.Exact3D.ExponentialDecayCriteria
public import Theorem.StatisticalMechanics.Code.Exact3D.IsingBridgeTargets


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingBridgeTargets.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Exact3D

def FKXAxisConnectionExactExponentialDecay
    (conn : ℕ → ℝ) (A m : ℝ) : Prop :=
  ∀ᶠ n in Filter.atTop, conn n = A * Real.exp (-(m * (n : ℝ)))


end Exact3D
end StatMech
