/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
public import Theorem.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
public import Theorem.Category.Atlas.v1.TensorCategories.code.GradedVec
public import Theorem.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
public import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
public import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
public import Structure.v1.Atlas.TensorCategories.code.BasedRings

@[expose] public section

open Finset


/-- A `ℤ₊`-ring `A` is unital if `1` belongs to its basis, i.e. the unit set `I₀` is a
singleton. -/
def ZPlusRingDef.IsUnital {ι : Type*} [DecidableEq ι] (A : ZPlusRingDef ι) : Prop :=
  ∃ u : ι, A.I₀ = {u}

