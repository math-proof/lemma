module
public import Mathlib
public import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
public import Theorem.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
public import Theorem.Category.Atlas.v1.TensorCategories.code.VecInstances
public import Theorem.Category.Atlas.v1.TensorCategories.code.VecPivotalConcrete
public import Theorem.Category.Atlas.v1.TensorCategories.code.VecSphericalConcrete
public import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
public import Theorem.v1.Atlas.TensorCategories.code.DualCoherenceBridge
public import Def.v1.Atlas.TensorCategories.code.VecPivotalConcrete.Part2
public import Theorem.v1.Atlas.TensorCategories.code.VecSphericalConcrete
open CategoryTheory Module TensorCategories VecInstances MonoidalCategory Category


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecPivotal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
universe u


/-- The canonical double-dual isomorphism `V ≅ (V*)*` in `FGModuleCat k`,
realized via the linear-algebraic evaluation equivalence. -/
noncomputable def vecDoubleDualIso (k : Type u) [Field k] (V : FGModuleCat k) :
    V ≅ (Vᘁ)ᘁ :=
  (Module.evalEquiv k V).toFGModuleCatIso

