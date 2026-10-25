/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.GrothendieckRingCategorical.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.GrothendieckRingCategorical
import Lemma.Category.Atlas.v1.TensorCategories.code.GradedVec
import Lemma.Category.Atlas.v1.TensorCategories.code.TannakaReconstruction
import Theorem.v1.Atlas.TensorCategories.code.GradedVec.Part6
import Structure.v1.Atlas.TensorCategories.code.TannakaReconstruction
import Structure.v1.Atlas.TensorCategories.code.BasedRings.Part2
open Finset


/-- A based ring is unital if the basis contains `1`, i.e. `I₀` is a singleton. -/
def BasedRingDef.IsUnital {ι : Type*} [DecidableEq ι] (B : BasedRingDef ι) : Prop :=
  ∃ u : ι, B.I₀ = {u}

