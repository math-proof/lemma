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
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec10SheavesP1.Part2


noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u v w

/-- Abstract axiomatization of locally free sheaves (= vector bundles) on `P¹_k`,
packaging rank, twisting sheaves `O(d)`, finite direct sums, and an isomorphism
relation. Used to formulate Grothendieck–Birkhoff splitting. -/
class ProjectiveLineBundle (k : Type u) [Field k] where
  LocallyFreeSheaf : Type u
  rank : LocallyFreeSheaf → ℕ
  twistingSheaf : ℤ → LocallyFreeSheaf
  directSum : (ι : Type) → [Fintype ι] → (ι → LocallyFreeSheaf) → LocallyFreeSheaf
  iso : LocallyFreeSheaf → LocallyFreeSheaf → Prop
  twistingSheaf_rank : ∀ d : ℤ, rank (twistingSheaf d) = 1
  iso_refl : ∀ E, iso E E
  iso_symm : ∀ E F, iso E F → iso F E
  iso_trans : ∀ E F G, iso E F → iso F G → iso E G

end
