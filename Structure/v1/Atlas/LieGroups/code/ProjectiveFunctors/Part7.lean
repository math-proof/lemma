/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
import Lemma.Int.WeightLE.of.BruhatLE
import Lemma.Int.FGUeaIotaRange
import Lemma.Int.IsCategoryOA.of.IsCategoryOB
import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
import Structure.v1.Atlas.LieGroups.code.TensorO
import Def.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part4


noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

structure IsProjectiveThetaFunctor {Δ : TriangularDecomposition R 𝔤}
    {wg : WeylGroupData Δ} {theta : Δ.𝔥 →ₗ[R] R}
    (F : ThetaFunctorData R 𝔤 Δ wg theta) : Prop where
  exists_tensor_summand :
    ∃ (FV : TensorFunctorData R 𝔤),
      IsDirectSummandTheta F (FV.restrictToTheta Δ wg theta)

end ProjectiveFunctors
end
