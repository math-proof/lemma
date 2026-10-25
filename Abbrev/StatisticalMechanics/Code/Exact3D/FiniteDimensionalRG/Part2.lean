/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteDimensionalRG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.RGBridgeCriteria
import Theorem.StatisticalMechanics.Code.Exact3D.MatrixCertificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part6


namespace StatMech

namespace Exact3D

namespace FiniteHyperbolicSplitting

abbrev hamiltonian {n : ℕ} (_H : FiniteHyperbolicSplitting n) :
    EffectiveHamiltonian where
  carrier := State n


end FiniteHyperbolicSplitting
end Exact3D
end StatMech
