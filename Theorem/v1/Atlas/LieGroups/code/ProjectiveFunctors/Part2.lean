module
public import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
public import Theorem.Int.WeightLE.of.BruhatLE
public import Theorem.Int.FGUeaIotaRange
public import Theorem.Int.IsCategoryOA.of.IsCategoryOB
public import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
public import Structure.v1.Atlas.LieGroups.code.TensorO
public import Structure.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

theorem hasInfChar_implies_hasGenInfChar {Δ : TriangularDecomposition R 𝔤}
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R)
    (h : HasInfChar M theta) : HasGenInfChar M theta :=
  ⟨centerActsByScalar_implies_nilpotentlyShifted Δ M theta h.center_acts_by_scalar⟩

end ProjectiveFunctors
end
