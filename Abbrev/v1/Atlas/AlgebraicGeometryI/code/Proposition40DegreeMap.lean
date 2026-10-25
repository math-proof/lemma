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
import Def.v1.Atlas.AlgebraicGeometryI.code.Proposition40DegreeMap
set_option maxHeartbeats 400000


noncomputable section

open CategoryTheory

namespace Proposition40

universe u v

attribute [instance] SmoothCompleteCurveCohData.catInst

attribute [instance] SmoothCompleteCurveCohData.abelInst

variable (D : SmoothCompleteCurveCohData.{u,v})

/-- The Grothendieck group `K⁰(Coh(X))` of coherent sheaves: the free abelian group on
coherent sheaves modulo the short exact sequence relations. -/
abbrev K0Coh : Type _ :=
  FreeAbelianGroup D.CohSheaf ⧸ CohSESRelSubgroup D

end Proposition40
end
