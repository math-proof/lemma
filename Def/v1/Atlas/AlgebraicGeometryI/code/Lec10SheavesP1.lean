/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10SheavesP1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.Stalks
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.Multiset.Sort
import Mathlib.AlgebraicGeometry.Modules.Tilde


noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u v w

/-- Definition 21 (Lec 10): a presheaf of objects of `C` on a topological space `X` is
a contravariant functor from `Opens X` to `C`. -/
def presheaf_def (C : Type u) [Category.{v} C] (X : TopCat.{w}) :=
  TopCat.Presheaf C X

/-- Definition 23 (Lec 10): the pushforward functor `f_*` on presheaves induced by a
continuous map `f : X → Y`, sending `F` to `U ↦ F(f⁻¹U)`. -/
def pushforward_presheaf_def (C : Type u) [Category.{v} C]
    {X Y : TopCat.{w}} (f : X ⟶ Y) :
    TopCat.Presheaf C X ⥤ TopCat.Presheaf C Y :=
  TopCat.Presheaf.pushforward C f

end
