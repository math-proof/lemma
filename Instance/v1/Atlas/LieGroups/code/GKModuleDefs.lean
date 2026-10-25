/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/GKModuleDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.GKModule.Part2
import Def.v1.Atlas.LieGroups.code.Admissible.Part3
import Lemma.Bijective.EqContinuousLinearEquivOfBijective.of.Bijective
import Mathlib.Algebra.Lie.Semisimple.Defs
import Structure.v1.Atlas.LieGroups.code.GKModuleDefs.Part2


noncomputable section

open scoped ComplexOrder

instance (SG : SemisimpleLieGroup) : Group SG.G := SG.instGroup

instance (SG : SemisimpleLieGroup) : TopologicalSpace SG.G := SG.instTopologicalSpace

instance (SG : SemisimpleLieGroup) : IsTopologicalGroup SG.G := SG.instIsTopologicalGroup

instance (SG : SemisimpleLieGroup) : LieRing SG.𝔤 := SG.instLieRing

instance (SG : SemisimpleLieGroup) : LieAlgebra ℝ SG.𝔤 := SG.instLieAlgebra

end
