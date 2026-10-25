/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Class.v1.Atlas.GeometryOfManifolds.code.HodgeTheory
set_option autoImplicit false

open DifferentialFormSpace


/-- Builds an `IsCompactOrientedRiemannian` structure on a compact symplectic manifold
(of real dimension $2n$) from explicit choices of codifferential, $L^2$ inner product,
volume form, Stokes data, and finite-dimensional harmonic spaces. -/
@[reducible] noncomputable def IsCompactSymplectic.toIsCompactOrientedRiemannian
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [h : IsCompactSymplectic Ω VF]
    (cod : Codifferential (inst := inst))
    (ip : @L2InnerProduct Ω VF inst cod)
    (vol : Ω (2 * h.n))
    (vol_nonzero : vol ≠ 0)
    (wedge_star : ∀ (p : ℕ), Ω p → Ω p → Ω (2 * h.n))
    (integrate : Ω (2 * h.n) → ℝ)
    (integrate_linear : ∀ (r : ℝ) (ω₁ ω₂ : Ω (2 * h.n)),
      integrate (r • ω₁ + ω₂) = r * integrate ω₁ + integrate ω₂)
    (stokes : ∀ (p : ℕ) (hp : p + 1 = 2 * h.n) (η : Ω p),
      integrate (hp ▸ inst.d η) = 0)

    (inner_eq : ∀ {p : ℕ} (α β : Ω p),
      ip.inner α β = integrate (wedge_star p α β))
    (finite_harmonic : ∀ (k : ℕ),
      ∃ (S : Finset (Ω (k + 1))),
        (∀ s ∈ S, IsHarmonic cod s) ∧
        (∀ (α : Ω (k + 1)), IsHarmonic cod α →
          ∃ (coeffs : Ω (k + 1) → ℝ),
            α = S.sum (fun s => coeffs s • s)))
    : IsCompactOrientedRiemannian Ω VF where
  dim := 2 * h.n
  dim_pos := Nat.mul_pos (by norm_num) h.n_pos
  cod := cod
  ip := ip
  vol := vol
  vol_nonzero := vol_nonzero
  wedge_star := wedge_star
  integrate := integrate
  integrate_linear := integrate_linear
  stokes_exact_vanishes := stokes
  inner_eq_integrate_wedge_star := inner_eq
  compact_finite_dim_harmonic := finite_harmonic

