module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec10SheavesP1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

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
public import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1


public section

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
