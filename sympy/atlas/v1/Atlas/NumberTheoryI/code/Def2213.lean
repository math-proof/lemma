/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Def2213.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.Ch22WeberLFunction
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ch22WeberLFunction
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Ch22ConductorDef
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Ch22ConductorDef

noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

def RayClassChar.kernelSubgroup {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) :
    Subgroup (FracIdealsCoprime K 𝔪) :=
  (MonoidHom.ker χ).comap (toRayClass K 𝔪)

def RayClassChar.kernelCongruenceSubgroup {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) :
    CongruenceSubgroupPair K where
  modulus := 𝔪
  subgroup := χ.kernelSubgroup
  ray_le := χ.rayGroup_le_kernelSubgroup

def RayClassChar.conductor {𝔪 : Modulus K} (χ : RayClassChar K 𝔪) : Modulus K :=
  χ.kernelCongruenceSubgroup.conductor
