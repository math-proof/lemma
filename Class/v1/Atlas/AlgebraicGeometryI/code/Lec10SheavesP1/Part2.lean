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
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1


noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u v w

/-- A sheaf of modules `M` is locally free of rank `n` (Def 26, Lec 10) if local
trivialization data exists, i.e. `M.LocallyFreeData n` is nonempty. -/
class SheafOfModules.IsLocallyFree
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{v}}
    [∀ (X : C), (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrpCat.{v}]
    [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    (M : SheafOfModules.{v} R) (n : ℕ) : Prop where
  nonempty_locallyFreeData : Nonempty (M.LocallyFreeData n)

end
