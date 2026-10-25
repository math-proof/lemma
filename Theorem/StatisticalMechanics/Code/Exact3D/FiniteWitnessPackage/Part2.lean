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
import Def.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteStableWitness

theorem fixedPoint_isFixed {n : ℕ} (S : FiniteStableWitness n) :
    S.map S.fixedPoint = S.fixedPoint :=
  S.contraction.fixedPoint_isFixed


theorem exists_unique_fixedPoint {n : ℕ} (S : FiniteStableWitness n) :
    ∃! p : Fin n → ℝ, S.map p = p :=
  S.contraction.exists_unique_fixedPoint


theorem fixedPoint_mem {n : ℕ} (S : FiniteStableWitness n) :
    FiniteContraction.ClosedBall
      S.contraction.center S.contraction.radius S.fixedPoint :=
  S.contraction.fixedPoint_mem_selected

end FiniteStableWitness
end Exact3D
end StatMech
