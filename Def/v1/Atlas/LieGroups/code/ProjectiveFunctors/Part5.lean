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
import Structure.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part7


noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

def NatTransThetaSpace {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : ThetaFunctorData R 𝔤 Δ wg theta) : Type _ :=
  NatTransData F₁.baseFunctor F₂.baseFunctor

def evalAtVerma {Δ : TriangularDecomposition R 𝔤} {wg : WeylGroupData Δ}
    {theta : Δ.𝔥 →ₗ[R] R}
    (F₁ F₂ : ThetaFunctorData R 𝔤 Δ wg theta)
    (Mverma : RepGfObj R 𝔤)
    (eta : NatTransThetaSpace F₁ F₂) :
    RepGfHom (F₁.baseFunctor.obj Mverma) (F₂.baseFunctor.obj Mverma) :=
  eta.app Mverma

end ProjectiveFunctors
end
