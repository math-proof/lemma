/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds
set_option autoImplicit false

open DifferentialFormSpace


/-- Records that a differential form space carries a positive half-dimension $n > 0$, so the
ambient symplectic manifold has total dimension $2n$. -/
class SymplecticManifoldDim (Ω : ℕ → Type*) (VF : Type*)
    [DifferentialFormSpace Ω VF] where
  n : ℕ
  n_pos : 0 < n

/-- Marks a $2n$-dimensional symplectic differential form space as **compact symplectic**: the
symplectic form $\omega$ is not exact and there is a top-degree volume form $\omega^n$ which is
also not exact. This abstracts the cohomological obstructions that hold on compact symplectic
manifolds. -/
class IsCompactSymplectic (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] extends SymplecticManifoldDim Ω VF where
  symplectic_not_exact : (S : SymplecticManifold Ω VF) → ¬ IsExact' VF S.ω
  vol : (S : SymplecticManifold Ω VF) → Ω (2 * toSymplecticManifoldDim.n - 1 + 1)
  volume_not_exact : (S : SymplecticManifold Ω VF) →
    ¬ (∃ β : Ω (2 * toSymplecticManifoldDim.n - 1),
      inst.d β = vol S)


