/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FiniteWitnessPackageExample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackage.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.TailSummabilityExample
import Def.StatisticalMechanics.Code.Exact3D.ToyRG.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.Hierarchical.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FiniteWitnessPackageExample.Part2
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackageExample

noncomputable def hierarchicalStableClosedBallCertificate :
    FiniteContraction.ClosedBallContractionCertificate
      (fun x i => RatInterval.matVec hierarchicalStableLinearization x i) :=
  FiniteContraction.closedBallContractionCertificate_of_rowSumContraction
    hierarchicalStableRowSumContraction
    hierarchicalStableLinearization_mem_intervals
    (0 : Fin 1 → ℝ)
    (radius := 0)
    (by norm_num [hierarchicalStableRowSumContraction])
    (by norm_num)
    (by
      simp [FiniteContraction.l1Dist, RatInterval.matVec,
        RatInterval.supNormVec])


noncomputable def hierarchicalStableWitness : FiniteStableWitness 1 where
  map := fun x i => RatInterval.matVec hierarchicalStableLinearization x i
  contraction := hierarchicalStableClosedBallCertificate


end FiniteWitnessPackageExample
end Exact3D
end StatMech
