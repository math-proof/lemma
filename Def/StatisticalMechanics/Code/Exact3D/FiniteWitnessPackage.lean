/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.Certificate.Part6
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteDimensionalRG.Part15
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteSupportCertificateConsequences
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilitySkeleton.Part5
import Structure.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteStableWitness

noncomputable def fixedPoint {n : ℕ} (S : FiniteStableWitness n) :
    Fin n → ℝ :=
  S.contraction.fixedPoint


end FiniteStableWitness
end Exact3D
end StatMech
