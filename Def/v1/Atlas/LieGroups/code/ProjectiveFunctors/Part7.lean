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
import Theorem.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part4


noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

def IsProjectiveFunctor.toThetaFunctorData
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F : EndoFunctorData R 𝔤) (hF : IsProjectiveFunctor F) :
    ThetaFunctorData R 𝔤 Δ wg lam where
  baseFunctor := F
  factors_through_block := projective_factors_through_block Δ wg lam F hF

end ProjectiveFunctors
end
