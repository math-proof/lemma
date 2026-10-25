/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec14QCohProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec14QCohProjective
open CategoryTheory Limits TopologicalSpace AlgebraicGeometry

universe u


noncomputable section

/-- Predicate for being a coherent sheaf of `O_X`-modules (Lec 10, Def 25 + finite
type). Placeholder — to be specialized to mathlib's coherence notion. -/
structure GrMod {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] where
  carrier : Type u
  [instAddCommGroup : AddCommGroup carrier]
  [instModule : Module A carrier]
  component : ℤ → AddSubgroup carrier
  internal : DirectSum.IsInternal component
  graded_smul : ∀ (n : ℕ) (d : ℤ) (a : A) (m : carrier),
    a ∈ (𝒜 n : Set A) → m ∈ component d → a • m ∈ component (↑n + d)

end
