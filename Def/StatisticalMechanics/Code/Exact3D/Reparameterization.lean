/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/Reparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.StatisticalMechanics.Code.Exact3D.PowerLawBridge
public import Theorem.StatisticalMechanics.Code.Exact3D.Reparameterization

@[expose] public section

namespace StatMech

namespace Exact3D

namespace LeftCriticalReparam

def linearMap {ι κ : Type*} (M : CriticalModel ι) (N : CriticalModel κ)
    (a : ℝ) (β : ℝ) : ℝ :=
  N.betaC - a * (M.betaC - β)


end LeftCriticalReparam
end Exact3D
end StatMech
