/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/ProjectiveFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.LieGroups.code.CategoryOII.Part3
public import Lemma.Int.WeightLE.of.BruhatLE
public import Lemma.Int.FGUeaIotaRange
public import Theorem.Int.IsCategoryOA.of.IsCategoryOB
public import Def.v1.Atlas.LieGroups.code.DufloJoseph.Part8
public import Structure.v1.Atlas.LieGroups.code.TensorO
public import Theorem.v1.Atlas.LieGroups.code.ProjectiveFunctors


public noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

structure HasInfChar {Δ : TriangularDecomposition R 𝔤}
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) : Prop where
  center_acts_by_scalar : centerActsByScalar_prop Δ M theta

structure HasGenInfChar {Δ : TriangularDecomposition R 𝔤}
    (M : RepGfObj R 𝔤) (theta : Δ.𝔥 →ₗ[R] R) : Prop where
  center_acts_nilpotently_shifted : centerActsNilpotentlyShifted_prop Δ M theta

end ProjectiveFunctors
end
