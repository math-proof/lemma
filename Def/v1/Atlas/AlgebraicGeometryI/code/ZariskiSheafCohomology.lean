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
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.ZariskiSheafCohomology
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace


noncomputable section

namespace ZariskiSheafCohomology

/-- The structure sheaf of a scheme viewed as a sheaf of additive abelian
groups on the Zariski site. -/
def schemeAbSheaf (X : Scheme) :
    Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat :=
  (Sheaf.composeAndSheafify
    (Opens.grothendieckTopology X.toTopCat) commRingToAddCommGrp).obj X.sheaf

/-- The `n`-th Zariski sheaf cohomology of the structure sheaf of `X`. -/
def sheafCohomology (X : Scheme) (n : ℕ) : Type :=
  (schemeAbSheaf X).H n

end ZariskiSheafCohomology
end
