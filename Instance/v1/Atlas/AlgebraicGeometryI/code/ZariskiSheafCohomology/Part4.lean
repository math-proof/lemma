/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ZariskiSheafCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Sites.Spaces
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Algebra.Category.Ring.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.ZariskiSheafCohomology.Part3
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace


noncomputable section

namespace ZariskiSheafCohomology

/-- The Zariski cohomology functor is additive in its sheaf argument. -/
instance zariskiCohomologyFunctor_additive (X : Scheme) (n : ℕ) :
    (zariskiCohomologyFunctor X n).Additive := by
  unfold zariskiCohomologyFunctor; infer_instance

end ZariskiSheafCohomology
end
