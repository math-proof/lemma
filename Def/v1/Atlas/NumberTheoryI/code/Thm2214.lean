module
public import Def.v1.Atlas.NumberTheoryI.code.Def2213
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Def2213
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.GlobalCFT
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Prop229
public import Structure.v1.Atlas.NumberTheoryI.code.GlobalCFT.Part3
public import Theorem.v1.Atlas.NumberTheoryI.code.Prop229


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2214.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped NumberField

open GlobalCFT

namespace RayClassField

universe u

variable {K : Type u} [Field K] [NumberField K]

def RayClassChar.IsPrimitive {m : Modulus K} (chi : RayClassChar K m) : Prop :=
  ∀ (m' : Modulus K) (h : m'.dvd m) (chi' : RayClassChar K m'),
    IsInducedBy K m' m h chi' chi → m' = m

end RayClassField
end
