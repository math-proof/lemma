/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2214.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.NumberTheoryI.code.Def2213
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Def2213
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.GlobalCFT
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Prop229
import sympy.atlas.v1.Atlas.NumberTheoryI.code.GlobalCFT
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Prop229

noncomputable section

open scoped NumberField
open GlobalCFT

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

def RayClassChar.IsPrimitive {m : Modulus K} (chi : RayClassChar K m) : Prop :=
  ∀ (m' : Modulus K) (h : m'.dvd m) (chi' : RayClassChar K m'),
    IsInducedBy K m' m h chi' chi → m' = m
