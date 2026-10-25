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
import Def.v1.Atlas.ArithmeticGeometry.code.FunctionFieldEquiv


noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace ArithmeticGeometry

namespace Thm19_2

variable (k : Type u) [Field k] [PerfectField k]

attribute [instance] FunctionFieldCat.fieldInst FunctionFieldCat.algInst

attribute [instance] SmProjCurve.isIntegral SmProjCurve.isProper SmProjCurve.isSmooth

instance SmProjCurve.algebraFunctionField (C : SmProjCurve k) :
    Algebra k C.toScheme.functionField :=
  (C.algebraMapHom k).hom.toAlgebra

instance FunctionFieldCat.toFunctionField_k (F : FunctionFieldCat k) :
    ArithmeticGeometry.FunctionField_k k F.carrier where
  finitelyGenerated := F.finitelyGenerated
  transcendenceDegreeOne := F.transcendenceDegreeOne
  algClosedInF := fun x hx => by
    have := F.algClosedInF x hx
    rwa [IntermediateField.mem_bot, Set.mem_range]

end Thm19_2
end ArithmeticGeometry
end
