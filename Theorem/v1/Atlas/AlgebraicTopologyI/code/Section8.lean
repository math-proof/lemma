/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.GroupTheory.QuotientGroup.Basic
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section8.Part2


namespace AlgebraicTopologyI

open AlgebraicTopologyI

/-- Taking the `i`th face commutes with pushforward along a continuous map: the
`i`th face of `f ∘ σ` equals `f` composed with the `i`th face of `σ`. -/
theorem SingularSimplex.map_face {n : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (i : Fin (n + 2)) (σ : SingularSimplex (n + 1) X) :
    SingularSimplex.face i (SingularSimplex.map f σ) =
    SingularSimplex.map f (SingularSimplex.face i σ) := by
  simp [SingularSimplex.face, SingularSimplex.map, ContinuousMap.comp_assoc]

/-- Naturality of the singular boundary map: pushforward along a continuous map
commutes with the boundary, i.e. `f_* ∘ d = d ∘ f_*`. -/
theorem SingularChains.map_comp_boundaryMap {n : ℕ} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y)) :
    (boundaryMap n Y).comp (SingularChains.map f) =
    (SingularChains.map f).comp (boundaryMap n X) := by
  apply FreeAbelianGroup.lift_ext
  intro σ
  show boundaryMap n Y (SingularChains.map f (FreeAbelianGroup.of σ)) =
    SingularChains.map f (boundaryMap n X (FreeAbelianGroup.of σ))
  simp only [SingularChains.map, boundaryMap]
  erw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of]
  rw [map_sum]
  congr 1
  ext i
  dsimp
  erw [map_zsmul (FreeAbelianGroup.map (SingularSimplex.map f)),
    FreeAbelianGroup.map_of_apply, SingularSimplex.map_face]


/-- The singular boundary squares to zero, `d ∘ d = 0`, so the singular chains form
a genuine chain complex. This is Theorem 1.5 applied to the singular complex. -/
theorem singularChainsInclusion_comm_boundary (n : ℕ) (X : Type*) [TopologicalSpace X]
    (A : Set X) :
    (boundaryMap n X).comp (singularChainsInclusion (n + 1) X A) =
    (singularChainsInclusion n X A).comp (boundaryMap n ↥A) :=
  SingularChains.map_comp_boundaryMap
    (n := n) (⟨Subtype.val, continuous_subtype_val⟩ : C(↥A, X))

end AlgebraicTopologyI
