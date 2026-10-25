/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/MoserDarboux.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticStandardBasis
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticEvenDim
import Theorem.v1.Atlas.GeometryOfManifolds.code.SymplecticStandardBasis
import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
set_option autoImplicit false

universe u_chart v_chart

open Module FiniteDimensional Finset
open SymplecticLinearAlgebra
open DifferentialFormSpace


/-- The standard symplectic form on $\mathbb{R}^{2n} = \mathbb{R}^n \times \mathbb{R}^n$:
$\omega_0((p_1, q_1), (p_2, q_2)) = \sum_i (p_{1,i} q_{2,i} - p_{2,i} q_{1,i})$. -/
noncomputable def stdSymplForm (n : ℕ) :
    LinearMap.BilinForm ℝ ((Fin n → ℝ) × (Fin n → ℝ)) :=
  LinearMap.mk₂ ℝ
    (fun u v => ∑ i : Fin n, (u.1 i * v.2 i - v.1 i * u.2 i))
    (by intro u v w; simp only [Prod.fst_add, Prod.snd_add]
        have key : ∀ i : Fin n, (u.1 + v.1) i * w.2 i - w.1 i * (u.2 + v.2) i =
          (u.1 i * w.2 i - w.1 i * u.2 i) + (v.1 i * w.2 i - w.1 i * v.2 i) := by
          intro i; simp [Pi.add_apply]; ring
        simp_rw [key, Finset.sum_add_distrib])
    (by intro c u v; simp only [Prod.smul_fst, Prod.smul_snd]
        have key : ∀ i : Fin n, (c • u.1) i * v.2 i - v.1 i * (c • u.2) i =
          c * (u.1 i * v.2 i - v.1 i * u.2 i) := by
          intro i; simp [Pi.smul_apply, smul_eq_mul]; ring
        simp_rw [key, ← Finset.mul_sum, smul_eq_mul])
    (by intro u v w; simp only [Prod.fst_add, Prod.snd_add]
        have key : ∀ i : Fin n, u.1 i * (v.2 + w.2) i - (v.1 + w.1) i * u.2 i =
          (u.1 i * v.2 i - v.1 i * u.2 i) + (u.1 i * w.2 i - w.1 i * u.2 i) := by
          intro i; simp [Pi.add_apply]; ring
        simp_rw [key, Finset.sum_add_distrib])
    (by intro c u v; simp only [Prod.smul_fst, Prod.smul_snd]
        have key : ∀ i : Fin n, u.1 i * (c • v.2) i - (c • v.1) i * u.2 i =
          c * (u.1 i * v.2 i - v.1 i * u.2 i) := by
          intro i; simp [Pi.smul_apply, smul_eq_mul]; ring
        simp_rw [key, ← Finset.mul_sum, smul_eq_mul])


/-- Two symplectic forms $\omega_0, \omega_1$ are **deformation equivalent** if there is a
continuous family $\omega_t$ of symplectic $2$-forms connecting them (closed and nondegenerate
for $t \in [0, 1]$). -/
def IsDeformationEquivalent
    {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF] [TopologicalSpace (Ω 2)]
    (ω₀ ω₁ : Ω 2) : Prop :=
  ∃ (ω : ℝ → Ω 2),
    Continuous ω ∧
    (∀ t ∈ Set.Icc 0 1, d VF (ω t) = 0) ∧
    (∀ t ∈ Set.Icc 0 1, Function.Injective (fun (X : VF) => ι X (ω t))) ∧
    ω 0 = ω₀ ∧ ω 1 = ω₁

/-- Two symplectic forms $\omega_0, \omega_1$ are **isotopic** if they are connected by a
continuous family $\omega_t$ of symplectic forms whose cohomology class is constant:
$[\omega_t - \omega_0] = 0$ in $H^2$, i.e., $\omega_t - \omega_0 = d\alpha$ for some $\alpha$. -/
def IsIsotopic
    {Ω : ℕ → Type*} {VF : Type*}
    [DifferentialFormSpace Ω VF] [TopologicalSpace (Ω 2)]
    (ω₀ ω₁ : Ω 2) : Prop :=
  ∃ (ω : ℝ → Ω 2),
    Continuous ω ∧
    (∀ t ∈ Set.Icc 0 1, d VF (ω t) = 0) ∧
    (∀ t ∈ Set.Icc 0 1, Function.Injective (fun (X : VF) => ι X (ω t))) ∧
    ω 0 = ω₀ ∧ ω 1 = ω₁ ∧
    (∀ t ∈ Set.Icc 0 1, ∃ α : Ω 1, ω t - ω₀ = d VF α)


