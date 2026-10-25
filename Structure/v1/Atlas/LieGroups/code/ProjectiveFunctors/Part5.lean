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
import Def.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part3


noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

structure TensorFunctorData (R : Type u) [CommRing R] (𝔤 : Type u) [LieRing 𝔤]
    [LieAlgebra R 𝔤] where
  V : Type u
  inst_addCommGroupV : AddCommGroup V
  inst_moduleV : Module R V
  inst_lieRingModuleV : LieRingModule 𝔤 V
  inst_lieModuleV : LieModule R 𝔤 V
  inst_finiteDimV : Module.Finite R V
  inst_freeV : Module.Free R V
  functor : EndoFunctorData R 𝔤
  tensor_obj_spec : ∀ (M : RepGfObj R 𝔤),
    Nonempty ((functor.obj M).carrier ≃ₗ⁅R, 𝔤⁆ (TensorProduct R V M.carrier))
  block_factoring : ∀ (Δ : TriangularDecomposition R 𝔤)
    (theta : Δ.𝔥 →ₗ[R] R) (M : RepGfObj R 𝔤),
    ¬ HasGenInfChar M theta → ∀ (x : (functor.obj M).carrier), x = 0
  is_exact : ∀ {M₁ M₂ M₃ : RepGfObj R 𝔤}
    (f : RepGfHom M₁ M₂) (g : RepGfHom M₂ M₃)
    (_hex : IsExactSequence f g),
    IsExactSequence (functor.mapHom f) (functor.mapHom g)
  sends_projectives_to_projectives : ∀ (M : RepGfObj R 𝔤),
    IsProjectiveModule M → IsProjectiveModule (functor.obj M)

structure IsProjectiveFunctor (F : EndoFunctorData R 𝔤) : Prop where
  exists_tensor_summand :
    ∃ (FV : TensorFunctorData R 𝔤), IsDirectSummand F FV.functor

end ProjectiveFunctors
end
