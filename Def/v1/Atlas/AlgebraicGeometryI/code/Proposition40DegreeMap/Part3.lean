/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Proposition40DegreeMap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.GroupTheory.QuotientGroup.Defs
import Theorem.v1.Atlas.AlgebraicGeometryI.code.Proposition40DegreeMap.Part2
set_option maxHeartbeats 400000


noncomputable section

open CategoryTheory

namespace Proposition40

universe u v

attribute [instance] SmoothCompleteCurveCohData.catInst

attribute [instance] SmoothCompleteCurveCohData.abelInst

variable (D : SmoothCompleteCurveCohData.{u,v})

/-- The induced degree homomorphism `δ : K⁰(Coh(X)) → ℤ`. -/
def degreeMapK0 : K0Coh D →+ ℤ :=
  QuotientAddGroup.lift (CohSESRelSubgroup D)
    (FreeAbelianGroup.lift D.degree)
    (degree_lift_ker_contains_relations D)

end Proposition40
end
