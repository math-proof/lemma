/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecSphericalConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
public import Theorem.Category.Atlas.v1.TensorCategories.code.VecInstances
public import Theorem.Category.Atlas.v1.TensorCategories.code.VecDualMapBridge
public import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
public import Theorem.v1.Atlas.TensorCategories.code.VecDualMapBridge

@[expose] public section

open CategoryTheory MonoidalCategory Module Category

universe u


attribute [-instance] RigidCategory.toRightRigidCategory

set_option maxHeartbeats 800000


noncomputable section

variable (k : Type u) [Field k]

/-- The concrete left quantum trace of a morphism `a : V ⟶ (V*)*` in `FGModuleCat k`,
obtained by composing the coevaluation, whiskering by `a`, and the evaluation. -/
def vecLeftQuantumTrace {V : FGModuleCat.{u} k} (a : V ⟶ (Vᘁ)ᘁ) :
    𝟙_ (FGModuleCat.{u} k) ⟶ 𝟙_ (FGModuleCat.{u} k) :=
  η_ V (Vᘁ) ≫ (a ▷ Vᘁ) ≫ ε_ (Vᘁ) ((Vᘁ)ᘁ)

/-- The concrete pivotal dimension of `V` in `FGModuleCat k`, defined as the left
quantum trace of the canonical double-dual evaluation iso `V ≅ (V*)*`. -/
def vecPivotalDim (V : FGModuleCat.{u} k) :
    𝟙_ (FGModuleCat.{u} k) ⟶ 𝟙_ (FGModuleCat.{u} k) :=
  vecLeftQuantumTrace k ((Module.evalEquiv k V).toFGModuleCatIso.hom)

end
