module
public import Def.v1.Atlas.GeometryOfManifolds.code.EuclideanDFS.Part3
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.EuclideanDFS
public import Theorem.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
public import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EuclideanSymplectic.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open EuclideanΩ

/-- Every element of `Fin 2` is either `0` or `1`. -/
lemma Fin2_eq_zero_or_one (k : Fin 2) : k = 0 ∨ k = 1 := by
  rcases k with ⟨k, hk⟩; simp only [Fin.ext_iff]; omega

end
