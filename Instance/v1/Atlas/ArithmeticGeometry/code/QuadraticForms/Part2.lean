/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/QuadraticForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.GroupTheory.QuotientGroup.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.QuadraticForms
open LinearMap (BilinMap BilinForm)


namespace QuadraticFormEquiv

section BilinQuadEquiv

variable {k : Type*} [Field k] [NeZero (2 : k)]

variable {V : Type*} [AddCommGroup V] [Module k V]

instance squaresSubgroupNormal : (squaresSubgroup k).Normal := Subgroup.normal_of_comm _

end BilinQuadEquiv
end QuadraticFormEquiv
