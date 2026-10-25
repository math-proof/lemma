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
import Def.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part6


noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

theorem projective_factors_through_block
    (Δ : TriangularDecomposition R 𝔤) (wg : WeylGroupData Δ)
    (lam : Δ.𝔥 →ₗ[R] R)
    (F : EndoFunctorData R 𝔤) (_hF : IsProjectiveFunctor F) :
    FactorsThroughBlock Δ F lam := by


  intro M hM x

  obtain ⟨FV, i, p, hpi⟩ := _hF.exists_tensor_summand

  have hret : (p.app M).toFun ((i.app M).toFun x) = x := by
    have := hpi M x
    simp only [NatTransData.comp, NatTransData.id, RepGfHom.comp, RepGfHom.id,
               LieModuleHom.coe_comp, Function.comp_apply, LieModuleHom.coe_id, id_eq] at this
    exact this

  have hzero : (i.app M).toFun x = (0 : (FV.functor.obj M).carrier) :=
    FV.block_factoring Δ lam M hM ((i.app M).toFun x)

  rw [← hret, hzero, map_zero]

end ProjectiveFunctors
end
