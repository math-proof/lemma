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
import Instance.v1.Atlas.AlgebraicGeometryI.code.ZariskiSheafCohomology.Part2
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace


noncomputable section

namespace ZariskiSheafCohomology

/-- Specialization to affine schemes: the `n`-th Zariski cohomology of
`Spec R`. -/
def specCohomology (R : CommRingCat) (n : ℕ) : Type :=
  sheafCohomology (Scheme.Spec.obj (Opposite.op R)) n

end ZariskiSheafCohomology
end
