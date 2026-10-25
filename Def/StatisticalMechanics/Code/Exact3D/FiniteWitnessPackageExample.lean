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
open scoped BigOperators


namespace StatMech

namespace Exact3D

namespace FiniteWitnessPackageExample

def exampleScale : BlockScale where
  L := 2
  one_lt := by norm_num


noncomputable def stableZeroWitness : FiniteStableWitness 1 where
  map := @FiniteContraction.zeroMap 1
  contraction :=
    FiniteContraction.zeroMap_closedBallContractionCertificate
      (n := 1) (radius := 0) (by norm_num)


end FiniteWitnessPackageExample
end Exact3D
end StatMech
