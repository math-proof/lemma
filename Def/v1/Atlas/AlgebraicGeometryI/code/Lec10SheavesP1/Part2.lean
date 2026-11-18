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

/-- The adjunction `M ↦ M̃ ⊣ Γ` between the tilde construction and global sections on
`Spec R`. -/
def tilde_gamma_adjunction (R : CommRingCat.{u}) :
    tilde.functor R ⊣ moduleSpecΓFunctor :=
  tilde.adjunction

/-- The tilde functor `M ↦ M̃` from `R`-modules to quasi-coherent sheaves on `Spec R`
is fully faithful. -/
def tilde_fullyFaithful (R : CommRingCat.{u}) :
    (tilde.functor R).FullyFaithful :=
  tilde.fullyFaithfulFunctor

end
