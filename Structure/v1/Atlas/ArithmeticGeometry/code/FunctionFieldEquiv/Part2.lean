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
import Instance.v1.Atlas.ArithmeticGeometry.code.FunctionFieldEquiv


noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace ArithmeticGeometry

namespace Thm19_2

variable (k : Type u) [Field k] [PerfectField k]

attribute [instance] FunctionFieldCat.fieldInst FunctionFieldCat.algInst

@[ext]
structure FunctionFieldCat.Hom (F₁ F₂ : FunctionFieldCat k) where
  toAlgHom : F₁.carrier →ₐ[k] F₂.carrier

end Thm19_2
end ArithmeticGeometry
end
