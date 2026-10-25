/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ReflexiveSheaves.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Contraction
import Mathlib.RingTheory.Ideal.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ReflexiveSheaves


noncomputable section

namespace ReflexiveSheaf

open Module

section ReflexivityCharacterization

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Free modules of finite rank are reflexive. -/
instance freeModule_isReflexive (n : ℕ) : IsReflexive R (Fin n → R) :=
  Module.instIsReflexiveOfFiniteOfProjective R _

end ReflexivityCharacterization
end ReflexiveSheaf
end
