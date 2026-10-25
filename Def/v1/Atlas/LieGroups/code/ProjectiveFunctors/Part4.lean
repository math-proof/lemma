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
import Structure.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part6


noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

def AreNatIsoTheta {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F G : ThetaFunctorData R 𝔤 Δ wg theta) : Prop :=
  AreNatIso F.baseFunctor G.baseFunctor

def IsDirectSummandTheta {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F G : ThetaFunctorData R 𝔤 Δ wg theta) : Prop :=
  IsDirectSummand F.baseFunctor G.baseFunctor

def TensorFunctorData.restrictToTheta (FV : TensorFunctorData R 𝔤)
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (theta : Δ.𝔥 →ₗ[R] R) : ThetaFunctorData R 𝔤 Δ wg theta where
  baseFunctor := FV.functor
  factors_through_block := FV.block_factoring Δ theta

end ProjectiveFunctors
end
