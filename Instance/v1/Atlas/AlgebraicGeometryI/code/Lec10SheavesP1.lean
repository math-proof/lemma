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
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u v w

/-- Presheaves of abelian groups on `X` form an abelian category. -/
instance presheaf_category_abelian (X : TopCat.{u}) :
    Abelian (TopCat.Presheaf AddCommGrpCat.{u} X) :=
  inferInstance

/-- Sheaves of abelian groups on `X` form an abelian category. -/
instance sheaf_category_abelian (X : TopCat.{u}) :
    Abelian (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstance

/-- Proposition 15 (Lec 11): sheafification is a left adjoint and therefore preserves
all colimits. -/
instance sheafification_preserves_colimits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (D : Type*) [Category D] [HasWeakSheafify J D] :
    PreservesColimitsOfSize.{v, v} (presheafToSheaf J D) :=
  (sheafificationAdjunction J D).leftAdjoint_preservesColimits

/-- Sheafification is exact: in addition to preserving colimits, it also preserves
finite limits. -/
instance sheafification_preserves_finite_limits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (D : Type*) [Category D] [HasSheafify J D] :
    PreservesFiniteLimits (presheafToSheaf J D) :=
  inferInstance

end
