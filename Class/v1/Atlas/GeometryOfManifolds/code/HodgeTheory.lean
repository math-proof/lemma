/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part7
set_option autoImplicit false

open DifferentialFormSpace


/-- A compact manifold of positive dimension `dim`. -/
class IsCompactManifold (Ω : ℕ → Type*) (VF : Type*)
    [DifferentialFormSpace Ω VF] where
  dim : ℕ
  dim_pos : 0 < dim

/-- A compact oriented Riemannian manifold equipped with a codifferential, an $L^2$
inner product, a volume form, Stokes' theorem for exact forms, and the integral formula
$\langle \alpha, \beta\rangle = \int_M \alpha \wedge *\beta$. Also assumes finite
dimensionality of harmonic forms in each degree. -/
class IsCompactOrientedRiemannian (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] extends IsCompactManifold Ω VF where
  cod : @Codifferential Ω VF inst
  ip : @L2InnerProduct Ω VF inst cod
  vol : Ω dim
  vol_nonzero : vol ≠ 0
  wedge_star : ∀ (p : ℕ), Ω p → Ω p → Ω dim
  integrate : Ω dim → ℝ
  integrate_linear : ∀ (r : ℝ) (ω₁ ω₂ : Ω dim),
    integrate (r • ω₁ + ω₂) = r * integrate ω₁ + integrate ω₂

  stokes_exact_vanishes : ∀ (p : ℕ) (hp : p + 1 = dim) (η : Ω p),
    integrate (hp ▸ inst.d η) = 0

  inner_eq_integrate_wedge_star : ∀ {p : ℕ} (α β : Ω p),
    ip.inner α β = integrate (wedge_star p α β)
  compact_finite_dim_harmonic : ∀ (k : ℕ),
    ∃ (S : Finset (Ω (k + 1))),
      (∀ s ∈ S, IsHarmonic cod s) ∧
      (∀ (α : Ω (k + 1)), IsHarmonic cod α →
        ∃ (coeffs : Ω (k + 1) → ℝ),
          α = S.sum (fun s => coeffs s • s))


