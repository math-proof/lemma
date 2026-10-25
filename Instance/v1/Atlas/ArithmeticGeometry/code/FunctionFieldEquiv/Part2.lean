/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FunctionFieldEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ArithmeticGeometry.code.CurveTheory.Part10
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.CurveTheory
import Structure.v1.Atlas.ArithmeticGeometry.code.FunctionFieldEquiv.Part2


noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace ArithmeticGeometry

namespace Thm19_2

variable (k : Type u) [Field k] [PerfectField k]

attribute [instance] FunctionFieldCat.fieldInst FunctionFieldCat.algInst

instance : Category (FunctionFieldCat k) where
  Hom F₁ F₂ := FunctionFieldCat.Hom k F₁ F₂
  id F := ⟨AlgHom.id k F.carrier⟩
  comp f g := ⟨g.toAlgHom.comp f.toAlgHom⟩

end Thm19_2
end ArithmeticGeometry
end
