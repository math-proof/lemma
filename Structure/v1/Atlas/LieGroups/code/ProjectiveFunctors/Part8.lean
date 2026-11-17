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
public import Def.v1.Atlas.LieGroups.code.ProjectiveFunctors.Part5


public noncomputable section

open scoped TensorProduct

universe u

namespace ProjectiveFunctors

variable {R : Type u} [CommRing R]

variable {𝔤 : Type u} [LieRing 𝔤] [LieAlgebra R 𝔤]

attribute [instance] RepGfObj.inst_addCommGroup RepGfObj.inst_module
  RepGfObj.inst_lieRingModule RepGfObj.inst_lieModule

structure NatTransOnInfChar {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F₁ F₂ : EndoFunctorData R 𝔤) where
  app : ∀ (M : RepGfObj R 𝔤), HasInfChar M theta → RepGfHom (F₁.obj M) (F₂.obj M)
  naturality : ∀ {M₁ M₂ : RepGfObj R 𝔤} (hM₁ : HasInfChar M₁ theta)
    (hM₂ : HasInfChar M₂ theta) (f : RepGfHom M₁ M₂),
    ((app M₂ hM₂).comp (F₁.mapHom f)).EqAsMap ((F₂.mapHom f).comp (app M₁ hM₁))

structure NatTransOnGenInfChar {Δ : TriangularDecomposition R 𝔤}
    (theta : Δ.𝔥 →ₗ[R] R) (F₁ F₂ : EndoFunctorData R 𝔤) where
  app : ∀ (M : RepGfObj R 𝔤), HasGenInfChar M theta → RepGfHom (F₁.obj M) (F₂.obj M)
  naturality : ∀ {M₁ M₂ : RepGfObj R 𝔤} (hM₁ : HasGenInfChar M₁ theta)
    (hM₂ : HasGenInfChar M₂ theta) (f : RepGfHom M₁ M₂),
    ((app M₂ hM₂).comp (F₁.mapHom f)).EqAsMap ((F₂.mapHom f).comp (app M₁ hM₁))

end ProjectiveFunctors
end
