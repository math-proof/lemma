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
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1


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
