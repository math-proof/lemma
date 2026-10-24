/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop22_4_RayClassGroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.RayClassFields
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Cor227
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GlobalCFT
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Cor227
import sympy.atlas.v1.Atlas.NumberTheoryI.code.GlobalCFT

open RayClassField GlobalCFT

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
