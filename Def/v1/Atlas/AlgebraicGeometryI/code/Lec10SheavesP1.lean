/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10SheavesP1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.Data.Multiset.Sort
public import Mathlib.AlgebraicGeometry.Modules.Tilde

@[expose] public section

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
