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
public import Def.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1.Part2

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u v w

/-- Instance: `tilde.functor R` is a left adjoint (to global sections on `Spec R`). -/
instance tilde_isLeftAdjoint_inst (R : CommRingCat.{u}) :
    (tilde.functor R).IsLeftAdjoint :=
  tilde.adjunction.isLeftAdjoint

end
