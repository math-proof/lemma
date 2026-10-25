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
import Instance.v1.Atlas.AlgebraicGeometryI.code.ZariskiSheafCohomology.Part3
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace


noncomputable section

namespace ZariskiSheafCohomology

/-- Degree-zero cohomology is identified with `Hom`-out of the constant sheaf
on `ℤ`, via the `Ext⁰` formalism. -/
def h0AddEquivHom (X : Scheme) :
    sheafCohomology X 0 ≃+
      ((constantSheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ schemeAbSheaf X) :=
  Ext.addEquiv₀

/-- Adjunction equivalence: morphisms from the constant sheaf on `ℤ` to a
sheaf correspond to global sections of that sheaf. -/
def h0EquivSections (X : Scheme) :
    ((constantSheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶ schemeAbSheaf X) ≃
      (AddCommGrpCat.of (ULift ℤ) ⟶
        ((sheafSections (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat).obj
          (Opposite.op ⊤)).obj (schemeAbSheaf X)) :=
  (constantSheafAdj (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat
    Limits.isTerminalTop).homEquiv _ _

/-- The functor `F ↦ Hⁿ(X, F)` taking a sheaf to its `n`-th Zariski sheaf
cohomology. -/
def zariskiCohomologyFunctor (X : Scheme) (n : ℕ) :
    Sheaf (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat ⥤ AddCommGrpCat :=
  Sheaf.cohomologyFunctor (Opens.grothendieckTopology X.toTopCat) n

end ZariskiSheafCohomology
end
