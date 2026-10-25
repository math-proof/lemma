/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Reflection/ReflectionGroupsCoxeter.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Reflection.HyperplaneChambers.Part4
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Nat.Lattice
import Def.v1.Atlas.Buildings.code.Reflection.ReflectionGroupsCoxeter
open scoped InnerProductSpace
open Set


noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

namespace HyperplaneArrangement

/-- A *Coxeter arrangement* is a hyperplane arrangement equipped with the package of axioms
needed to identify the reflection group as a Coxeter group. The axioms include: reflections
permute chambers, are involutions, act transitively (and via wall-reflections) on chambers, are
faithful, the closure of one chamber tiles space, distinct translates of the open chamber are
disjoint, an Exchange property holds, wall reflections in adjacent chambers are conjugate,
length is bounded by gallery distance both above and below, walls of a reduced word fix the
right points, a reflection through a wall of $C$ is a wall of any chamber it produces, wall
reflections fix points of their carriers, and the dihedral subgroups are locally finite (Cartan
integrality). -/
class CoxeterArrangement (arr : HyperplaneArrangement E) where
  reflection_maps_chambers :
    ∀ η ∈ arr.hyperplanes, ∀ C : arr.Chamber,
      ∃ D : arr.Chamber, D.set = imageByIsometry η.reflectionMap C.set
  reflection_involutive :
    ∀ η ∈ arr.hyperplanes, η.reflectionMap * η.reflectionMap = 1
  transitive_on_chambers :
    ∀ C D : arr.Chamber, ∃ w : arr.ReflectionGroup,
      imageByIsometry w.val C.set = D.set
  transitive_via_wall_reflections :
    ∀ C D : arr.Chamber, ∃ w ∈ arr.WallReflectionGroup C,
      imageByIsometry w C.set = D.set
  faithful_on_chambers :
    ∀ (C : arr.Chamber) (w : arr.ReflectionGroup),
      imageByIsometry w.val C.set = C.set → w = ⟨1, one_mem _⟩
  closure_covers :
    ∀ (C : arr.Chamber) (x : E),
      ∃ w ∈ arr.ReflectionGroup, x ∈ imageByIsometry w (closure C.set)
  open_chambers_disjoint :
    ∀ (C : arr.Chamber) (w₁ w₂ : arr.ReflectionGroup), w₁ ≠ w₂ →
      imageByIsometry w₁.val C.set ∩ imageByIsometry w₂.val C.set = ∅
  exchange_property :
    ∀ (C : arr.Chamber) (s : E ≃ᵃⁱ[ℝ] E), s ∈ arr.wallReflections C →
    ∀ (word : List (E ≃ᵃⁱ[ℝ] E)),
      (∀ t ∈ word, t ∈ arr.wallReflections C) →
      arr.IsWordFor C word word.prod →
      arr.wordLength C (s * word.prod) ≤ arr.wordLength C word.prod →
      ∃ i : Fin word.length,
        (s * word.prod) = (word.eraseIdx i.val).prod
  wall_reflection_conjugate :
    ∀ (C : arr.Chamber) (w : E ≃ᵃⁱ[ℝ] E), w ∈ arr.WallReflectionGroup C →
      ∀ (D : arr.Chamber), imageByIsometry w C.set = D.set →
        ∀ t ∈ arr.wallReflections D,
          ∃ s ∈ arr.wallReflections C, t = w * s * w⁻¹
  gallery_upper_bound :
    ∀ (C : arr.Chamber) (word : List (E ≃ᵃⁱ[ℝ] E)),
      (∀ s ∈ word, s ∈ arr.wallReflections C) →
      ∀ x ∈ C.set,
        arr.galleryDistance x (word.prod x) ≤ word.length
  gallery_lower_bound :
    ∀ (C : arr.Chamber) (w : E ≃ᵃⁱ[ℝ] E), w ∈ arr.ReflectionGroup →
      ∀ x ∈ C.set,
        arr.wordLength C w ≤ arr.galleryDistance x (w x)
  closure_wall_membership :
    ∀ (C : arr.Chamber) (s₁ : E ≃ᵃⁱ[ℝ] E) (rest : List (E ≃ᵃⁱ[ℝ] E)),
      s₁ ∈ arr.wallReflections C →
      (∀ t ∈ rest, t ∈ arr.wallReflections C) →
      arr.wordLength C ((s₁ :: rest).prod) = (s₁ :: rest).length →
      ∀ x ∈ closure C.set, (s₁ :: rest).prod x = x →
      ∃ η ∈ arr.walls C, s₁ = η.reflectionMap ∧ x ∈ η.carrier
  reflection_creates_wall :
    ∀ (η : AffineHyperplane E), η ∈ arr.hyperplanes →
      ∀ (C D : arr.Chamber), D.set = imageByIsometry η.reflectionMap C.set →
        η.IsWall D.set
  wall_reflection_fixes_wall_point :
    ∀ (η : AffineHyperplane E), η ∈ arr.hyperplanes →
      ∀ x ∈ η.carrier, η.reflectionMap x = x
  locally_finite :
    ∀ (C : arr.Chamber) (η ζ : AffineHyperplane E),
      η ∈ arr.hyperplanes → ζ ∈ arr.hyperplanes →
      η.IsWall C.set → ζ.IsWall C.set →
      ∃ n : ℤ, (2 : ℝ) * ⟪(‖η.normal‖⁻¹) • η.normal, (‖ζ.normal‖⁻¹) • ζ.normal⟫_ℝ = ↑n

end HyperplaneArrangement
end
