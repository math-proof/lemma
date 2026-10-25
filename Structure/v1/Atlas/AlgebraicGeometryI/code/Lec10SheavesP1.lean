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
import Class.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1


noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u v w

/-- Every line bundle on `P¹_k` is isomorphic to some twisting sheaf `O(d)`. -/
structure SheafOfModules.LocallyFreeData
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{v}}
    [∀ (X : C), (J.over X).HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    [∀ (X : C), HasWeakSheafify (J.over X) AddCommGrpCat.{v}]
    [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{v}]
    (M : SheafOfModules.{v} R) (n : ℕ) where
  I : Type u
  X : I → C
  coversTop : J.CoversTop X
  iso (i : I) : M.over (X i) ≅ SheafOfModules.free (ULift.{v} (Fin n))

end
