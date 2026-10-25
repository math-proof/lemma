/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/AffineWeylGroups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part4
import Theorem.v1.Atlas.Buildings.code.Reflection.WallSeparationCorollary
import Structure.v1.Atlas.Buildings.code.Reflection.AffineWeylGroups
set_option maxHeartbeats 800000

open scoped InnerProductSpace
open Set

set_option maxHeartbeats 800000


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace AffineReflectionGroup

variable (W : AffineReflectionGroup E)

/-- An alcove is a chamber of the underlying hyperplane arrangement. -/
def Alcove := W.arrangement.Chamber

/-- A point $x$ is *good* if it lies in the complement of every reflecting hyperplane. -/
def GoodPoint (x : E) : Prop :=
  x ∈ W.arrangement.complement

/-- A point $x$ is *special* if for every hyperplane $η$ of the arrangement there is a
parallel hyperplane $η'$ in the arrangement passing through $x$. -/
def SpecialPoint (x : E) : Prop :=
  ∀ η ∈ W.arrangement.hyperplanes,
    ∃ η' ∈ W.arrangement.hyperplanes,
      (∃ t : ℝ, η'.normal = t • η.normal) ∧ x ∈ η'.carrier

/-- The linear part subgroup is the image of $W$ under the linear-part homomorphism. -/
def LinearPartGroup : Subgroup (E ≃ₗᵢ[ℝ] E) :=
  W.group.map linearPartHom

/-- The translation subgroup of $W$: those elements with trivial linear part. -/
def TranslationSubgroup : Subgroup (E ≃ᵃⁱ[ℝ] E) :=
  W.group ⊓ linearPartHom.ker

/-- The group $W$ is *essential* if its linear part has no nonzero fixed vector. -/
def IsEssential : Prop :=
  ∀ v : E, (∀ wbar ∈ W.LinearPartGroup, wbar v = v) → v = 0

/-- The group $W$ is *indecomposable* if its set of reflections cannot be partitioned into
two pairwise-commuting nonempty subsets. -/
def IsIndecomposable : Prop :=
  let reflections := {s | s ∈ W.group ∧ ∃ η ∈ W.arrangement.hyperplanes,
    (∀ y ∈ η.carrier, s y = y) ∧ s * s = 1 ∧ s ≠ 1}
  ∀ (S1 S2 : Set (E ≃ᵃⁱ[ℝ] E)),
    S1 ⊆ reflections → S2 ⊆ reflections →
    (∀ s1 ∈ S1, ∀ s2 ∈ S2, s1 * s2 = s2 * s1) →
    S1 ∪ S2 = reflections →
    S1 = ∅ ∨ S2 = ∅

/-- Intersection of $n+1$ open half-spaces $\{x : ⟨n_i, x⟩ > c_i\}$. -/
def openHalfSpaceIntersection (n : ℕ) (normals : Fin (n + 1) → E)
    (offsets : Fin (n + 1) → ℝ) : Set E :=
  ⋂ i, {x : E | ⟪normals i, x⟫_ℝ > offsets i}

/-- Any chamber of a locally finite hyperplane arrangement is an intersection of finitely
many open half-spaces. -/
def separatingHyperplanes (W : AffineReflectionGroup E)
    (C D : W.arrangement.Chamber) : Set (AffineHyperplane E) :=
  { η ∈ W.arrangement.hyperplanes |
    ∃ c, c ∈ C.set ∧ ∃ d, d ∈ D.set ∧ η.Separates c d }

end AffineReflectionGroup


/-- If $A$ is described as the intersection of open half-spaces with given normals, then
the normal of any wall of $A$ is parallel to one of these defining normals. -/
noncomputable def normalLinearCombinationMap {m : ℕ} (normals : Fin (m + 1) → E) :
    (Fin (m + 1) → ℝ) →ₗ[ℝ] E :=
  Fintype.linearCombination ℝ normals

/-- The integer-linear span $\mathbb Z Φ$ of a set of roots $Φ$ is the root lattice. -/
def RootLattice (Φ : Set E) : Submodule ℤ E :=
  Submodule.span ℤ Φ

end
