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
import Def.v1.Atlas.AlgebraicGeometryI.code.ReflexiveSheaves.Part2


noncomputable section

namespace ReflexiveSheaf

open Module

section RankOneDual

variable (R : Type*) [CommRing R]

/-- An invertible sheaf (here represented as the rank-one free module) is reflexive. -/
instance invertibleSheaf_isReflexive : IsReflexive R (Fin 1 → R) :=
  Module.instIsReflexiveOfFiniteOfProjective R _

end RankOneDual
end ReflexiveSheaf
end
