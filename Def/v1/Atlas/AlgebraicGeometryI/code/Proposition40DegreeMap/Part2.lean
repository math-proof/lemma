/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Proposition40DegreeMap.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Abbrev.v1.Atlas.AlgebraicGeometryI.code.Proposition40DegreeMap

@[expose] public section

set_option maxHeartbeats 400000


noncomputable section

open CategoryTheory

namespace Proposition40

universe u v

attribute [instance] SmoothCompleteCurveCohData.catInst

attribute [instance] SmoothCompleteCurveCohData.abelInst

variable (D : SmoothCompleteCurveCohData.{u,v})

/-- The class `[ℱ] ∈ K⁰(Coh(X))` of a coherent sheaf `ℱ`. -/
def K0Coh.classOf (ℱ : D.CohSheaf) : K0Coh D :=
  QuotientAddGroup.mk (FreeAbelianGroup.of ℱ)

end Proposition40
end
