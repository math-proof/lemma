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
import Structure.v1.Atlas.ArithmeticGeometry.code.FunctionFieldEquiv.Part3


noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace ArithmeticGeometry

namespace Thm19_2

variable (k : Type u) [Field k] [PerfectField k]

attribute [instance] FunctionFieldCat.fieldInst FunctionFieldCat.algInst

attribute [instance] SmProjCurve.isIntegral SmProjCurve.isProper SmProjCurve.isSmooth

instance SmProjCurve.categoryInstance : Category (SmProjCurve k) where
  Hom C₁ C₂ := SmProjCurve.Hom k C₁ C₂
  id C := ⟨𝟙 C.toScheme, by simp⟩
  comp f g := ⟨f.toSchemeHom ≫ g.toSchemeHom, by
    rw [Category.assoc, g.over_spec, f.over_spec]⟩
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]

end Thm19_2
end ArithmeticGeometry
end
