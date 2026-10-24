/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Lem225.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields

noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

def RayGroup.toAmbientSubgroup (K : Type u) [Field K] [NumberField K]
    (𝔪 : Modulus K) : Subgroup (FracIdeal K)ˣ :=
  (RayGroup K 𝔪).map (FracIdealsCoprime_subgroup K 𝔪).subtype
