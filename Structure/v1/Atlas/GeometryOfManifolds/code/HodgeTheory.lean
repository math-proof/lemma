/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
set_option autoImplicit false

open DifferentialFormSpace


/-- A complex-linear structure on the spaces of differential forms.

Equips each $\Omega^p$ with a scalar multiplication by $\mathbb{C}$ compatible with
the existing $\mathbb{R}$-module structure. -/
structure HasComplexStructure
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  complexSmul : ∀ {p : ℕ}, ℂ → Ω p → Ω p
  complexSmul_add : ∀ {p : ℕ} (z : ℂ) (ω₁ ω₂ : Ω p),
    complexSmul z (ω₁ + ω₂) = complexSmul z ω₁ + complexSmul z ω₂
  complexSmul_zero : ∀ {p : ℕ} (ω : Ω p), complexSmul 0 ω = 0
  complexSmul_mul : ∀ {p : ℕ} (z w : ℂ) (ω : Ω p),
    complexSmul z (complexSmul w ω) = complexSmul (z * w) ω
  complexSmul_one : ∀ {p : ℕ} (ω : Ω p), complexSmul 1 ω = ω
  complexSmul_real : ∀ {p : ℕ} (r : ℝ) (ω : Ω p),
    complexSmul (r : ℂ) ω = r • ω


/-- The Hodge star operator $*: \Omega^p \to \Omega^p$ (a simplified involution version);
on an oriented Riemannian $n$-manifold it normally maps $\Omega^k \to \Omega^{n-k}$. -/
structure HodgeStar
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  star : ∀ {p : ℕ}, Ω p → Ω p
  star_star : ∀ {p : ℕ} (α : Ω p), star (star α) = α


/-- The codifferential $d^*: \Omega^k \to \Omega^{k-1}$, the formal $L^2$-adjoint of $d$.

On an oriented Riemannian $n$-manifold, $d^* = (-1)^{n(k-1)+1} * d *$ where $*$ is the
Hodge star and the sign factor satisfies $(\text{sign})^2 = 1$. -/
structure Codifferential
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  dstar : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  dstar_add : ∀ {p : ℕ} (α β : Ω (p + 1)), dstar (α + β) = dstar α + dstar β
  dstar_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), dstar (r • α) = r • dstar α
  hodge : HodgeStar (inst := inst)
  sign_factor : ℕ → ℝ
  sign_factor_sq : ∀ k, sign_factor k ^ 2 = 1
  manifold_dim : ℕ
  sign_factor_formula : ∀ k, sign_factor k = (-1 : ℝ) ^ (manifold_dim * (k - 1) + 1)
  star_deg : ∀ {k : ℕ}, k ≤ manifold_dim → Ω k → Ω (manifold_dim - k)
  star_deg_star_deg : ∀ {k : ℕ} (hk : k ≤ manifold_dim)
    (hk' : manifold_dim - k ≤ manifold_dim := by omega) (α : Ω k),
    cast (by congr 1; omega) (star_deg hk' (star_deg hk α)) = α
  dstar_formula : ∀ {p : ℕ} (h : p + 1 ≤ manifold_dim) (ω : Ω (p + 1)),
    dstar ω = sign_factor (p + 1) •
      cast (by congr 1; omega)
        (star_deg (by omega : manifold_dim - (p + 1) + 1 ≤ manifold_dim)
          (inst.d (star_deg h ω)))
  dstar_squared : ∀ {p : ℕ} (ω : Ω (p + 2)), dstar (dstar ω) = 0

