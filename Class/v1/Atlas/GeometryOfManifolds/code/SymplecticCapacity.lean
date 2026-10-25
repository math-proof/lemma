/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticCapacity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticCapacity
set_option autoImplicit false

open DifferentialFormSpace


/-- Marker class identifying a symplectic manifold $S$ as the standard symplectic ball $B^{2n}(r)$ of radius $r > 0$. -/
class IsSymplecticBall {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF] (S : SymplecticManifold Ω VF) where
  radius : ℝ
  halfDim : ℕ
  radius_pos : 0 < radius
  halfDim_pos : 0 < halfDim
  ω_exact : IsExact' VF S.ω
  capacity_val : NNReal
  capacity_eq : capacity_val = symplCapacity radius

/-- Marker class identifying a symplectic manifold $S$ as the standard symplectic cylinder $Z^{2n}(r) = B^2(r) \times \mathbb{R}^{2n-2}$. -/
class IsSymplecticCylinder {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF] (S : SymplecticManifold Ω VF) where
  radius : ℝ
  halfDim : ℕ
  radius_pos : 0 < radius
  halfDim_pos : 0 < halfDim
  ω_exact : IsExact' VF S.ω
  capacity_val : NNReal
  capacity_eq : capacity_val = symplCapacity radius


