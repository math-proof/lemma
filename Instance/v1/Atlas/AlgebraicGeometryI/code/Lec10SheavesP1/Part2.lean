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
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1.Part2


noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u v w

/-- Instance: `tilde.functor R` is a left adjoint (to global sections on `Spec R`). -/
instance tilde_isLeftAdjoint_inst (R : CommRingCat.{u}) :
    (tilde.functor R).IsLeftAdjoint :=
  tilde.adjunction.isLeftAdjoint

end
