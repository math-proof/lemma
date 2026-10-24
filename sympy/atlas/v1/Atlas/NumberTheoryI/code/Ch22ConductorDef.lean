/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Ch22ConductorDef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.Cor227
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor227

noncomputable section

open scoped NumberField

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

noncomputable def conductorModulus (p : CongruenceSubgroupPair K) : Modulus K :=
  (corollary_22_7_existence p).choose.modulus

def CongruenceSubgroupPair.conductor (p : CongruenceSubgroupPair K) : Modulus K :=
  conductorModulus p

def CongruenceSubgroupPair.IsPrimitive (p : CongruenceSubgroupPair K) : Prop :=
  p.modulus = p.conductor
