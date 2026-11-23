/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ZariskiSheafCohomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Algebra.Category.Ring.Basic
public import Instance.v1.Atlas.AlgebraicGeometryI.code.ZariskiSheafCohomology.Part2

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace


noncomputable section

namespace ZariskiSheafCohomology

/-- Specialization to affine schemes: the `n`-th Zariski cohomology of
`Spec R`. -/
def specCohomology (R : CommRingCat) (n : ℕ) : Type :=
  sheafCohomology (Scheme.Spec.obj (Opposite.op R)) n

end ZariskiSheafCohomology
end
