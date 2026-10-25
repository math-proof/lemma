/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKReparameterization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Reparameterization.Part2
import Theorem.StatisticalMechanics.Code.IsingFK.Q2.Part2
import Theorem.StatisticalMechanics.Code.Exact3D.FKReparameterization


namespace StatMech

namespace Exact3D

namespace FKReparameterization

noncomputable def pOfBetaDistancePrefactor (βc β : ℝ) : ℝ :=
  (IsingFK.pOfBeta βc - IsingFK.pOfBeta β) / (βc - β)


end FKReparameterization
end Exact3D
end StatMech
