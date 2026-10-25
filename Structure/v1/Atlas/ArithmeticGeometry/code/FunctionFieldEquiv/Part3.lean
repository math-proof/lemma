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
import Instance.v1.Atlas.ArithmeticGeometry.code.FunctionFieldEquiv.Part2


noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace ArithmeticGeometry

namespace Thm19_2

variable (k : Type u) [Field k] [PerfectField k]

attribute [instance] FunctionFieldCat.fieldInst FunctionFieldCat.algInst

structure SmProjCurve where
  toScheme : Scheme.{u}
  structureMorphism : toScheme ⟶ Spec (.of k)
  [isIntegral : IsIntegral toScheme]
  [isProper : IsProper structureMorphism]
  [isSmooth : SmoothOfRelativeDimension 1 structureMorphism]

attribute [instance] SmProjCurve.isIntegral SmProjCurve.isProper SmProjCurve.isSmooth

@[ext]
structure SmProjCurve.Hom (C₁ C₂ : SmProjCurve k) where
  toSchemeHom : C₁.toScheme ⟶ C₂.toScheme
  over_spec : toSchemeHom ≫ C₂.structureMorphism = C₁.structureMorphism

end Thm19_2
end ArithmeticGeometry
end
