/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecPivotal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
import Lemma.Category.Atlas.v1.TensorCategories.code.PivotalSpherical
import Lemma.Category.Atlas.v1.TensorCategories.code.VecInstances
import Lemma.Category.Atlas.v1.TensorCategories.code.VecPivotalConcrete
import Lemma.Category.Atlas.v1.TensorCategories.code.VecSphericalConcrete
import Abbrev.v1.Atlas.TensorCategories.code.VecInstances.Part2
import Theorem.v1.Atlas.TensorCategories.code.DualCoherenceBridge
import Def.v1.Atlas.TensorCategories.code.VecPivotalConcrete.Part2
import Theorem.v1.Atlas.TensorCategories.code.VecSphericalConcrete
open CategoryTheory Module TensorCategories VecInstances MonoidalCategory Category

universe u


/-- The canonical double-dual isomorphism `V ≅ (V*)*` in `FGModuleCat k`,
realized via the linear-algebraic evaluation equivalence. -/
noncomputable def vecDoubleDualIso (k : Type u) [Field k] (V : FGModuleCat k) :
    V ≅ (Vᘁ)ᘁ :=
  (Module.evalEquiv k V).toFGModuleCatIso

