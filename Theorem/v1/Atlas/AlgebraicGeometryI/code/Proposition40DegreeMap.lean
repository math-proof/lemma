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
public import Structure.v1.Atlas.AlgebraicGeometryI.code.Proposition40DegreeMap
set_option maxHeartbeats 400000

public section

noncomputable section

open CategoryTheory

namespace Proposition40

universe u v

attribute [instance] SmoothCompleteCurveCohData.catInst

attribute [instance] SmoothCompleteCurveCohData.abelInst

variable (D : SmoothCompleteCurveCohData.{u,v})

/-- Combining the two axioms in `SmoothCompleteCurveCohData`, the degree is additive on
*every* short exact sequence, not just locally free ones. -/
theorem degree_additive (S : ShortComplex D.CohSheaf) [Mono S.f] [Epi S.g]
    (hex : S.Exact) :
    D.degree S.X₂ = D.degree S.X₁ + D.degree S.X₃ := by

  obtain ⟨S', hf', hg', hex', hlf1, hlf2, hlf3, hdefect⟩ :=
    D.reduce_to_locally_free S hex

  have hlf := @SmoothCompleteCurveCohData.locally_free_additive D S' hf' hg' hex'
    hlf1 hlf2 hlf3

  omega

end Proposition40
end
