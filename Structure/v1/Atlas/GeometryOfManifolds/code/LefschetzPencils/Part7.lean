/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/LefschetzPencils.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.GeometryOfManifolds.code.AdvancedKahler.Part11
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.AdvancedKahler
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HodgeTheory
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part12
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Class.v1.Atlas.GeometryOfManifolds.code.LefschetzPencils.Part7
set_option autoImplicit false

open DifferentialFormSpace


/-- Data for the **adjunction formula** for a symplectic surface inside a 4-manifold:
the genus $g$, self-intersection $[\Sigma]\cdot[\Sigma]$, the value $\langle c_1, [\Sigma]\rangle$,
the first Chern numbers of the tangent and normal bundles, and the relations
- $c_1(T\Sigma) = 2 - 2g$ (Gauss-Bonnet),
- $c_1(N\Sigma) = [\Sigma]\cdot[\Sigma]$ (normal-bundle degree),
- $\langle c_1, [\Sigma]\rangle = c_1(T\Sigma) + c_1(N\Sigma)$ (splitting of $c_1(TM)|_\Sigma$). -/
structure HasAdjunctionData
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  genus : ℕ
  selfIntersection : ℤ
  c₁_eval : ℤ
  chern_tangent : ℤ
  chern_normal : ℤ
  gauss_bonnet_eq : chern_tangent = 2 - 2 * (genus : ℤ)
  normal_bundle_degree_eq : chern_normal = selfIntersection
  chern_split_eq : c₁_eval = chern_tangent + chern_normal


/-- Data for the **ramification locus** $R \subset X$ of a symplectic branched cover
$f: X \to Y$ and its image $D \subset Y$ (the branch divisor): inclusions $R
\hookrightarrow X$ and $D \hookrightarrow Y$, the restricted map $f|_R: R \to D$,
the property that $f^*\omega_Y$ degenerates along $R$, and the factorization
$f \circ \mathrm{incl}_R = \mathrm{incl}_D \circ (f|_R)$. -/
structure RamificationData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_Y : ℕ → Type*} {VF_Y : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_Y : DifferentialFormSpace Ω_Y VF_Y]
    (bc : SymplecticBranchedCovering (inst_X := inst_X) (inst_Y := inst_Y)) where
  Ω_R : ℕ → Type*
  VF_R : Type*
  [inst_R : DifferentialFormSpace Ω_R VF_R]
  Ω_D : ℕ → Type*
  VF_D : Type*
  [inst_D : DifferentialFormSpace Ω_D VF_D]
  inclR : @DFSMorphism Ω_R VF_R Ω_X VF_X inst_R inst_X
  inclD : @DFSMorphism Ω_D VF_D Ω_Y VF_Y inst_D inst_Y
  fRestrict : @DFSMorphism Ω_R VF_R Ω_D VF_D inst_R inst_D
  pullback_degenerate_on_R :
    ¬ Function.Injective (fun (v : VF_R) =>
        inst_R.ι v (inclR.pullback (bc.f.pullback bc.target.ω)))
  factorization : ∀ {p : ℕ} (α : Ω_Y p),
    inclR.pullback (bc.f.pullback α) = fRestrict.pullback (inclD.pullback α)


/-- A **symplectic form on a manifold $M$** in the manifold-with-corners formalism:
half the dimension, a skew-symmetric non-degenerate bilinear form on the model
space $E$. -/
structure ManifoldSymplecticForm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ⊤ M] where
  halfDim : ℕ
  form : E →L[ℝ] E →L[ℝ] ℝ
  skew : ∀ (v w : E), form v w = -(form w v)
  nondegenerate : Function.Injective form


/-- **Symplectic fiber-sum data** in the manifold-with-corners formalism: two
symplectic manifolds $M_1, M_2$ with a common codimension-2 submanifold $Q$,
smooth injective embeddings $\iota_j: Q \hookrightarrow M_j$, matching dimensions,
and chosen trivializations of the normal $\mathbb R^2$-bundles of $Q$ in $M_1$
and $M_2$ along the zero section. -/
structure FiberSum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M₁ M₂ Q : Type*)
    [TopologicalSpace M₁] [ChartedSpace H M₁] [IsManifold I ⊤ M₁]
    [TopologicalSpace M₂] [ChartedSpace H M₂] [IsManifold I ⊤ M₂]
    [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ⊤ Q] where
  ι₁ : Q → M₁
  ι₂ : Q → M₂
  ι₁_injective : Function.Injective ι₁
  ι₂_injective : Function.Injective ι₂
  ι₁_smooth : MDifferentiable I I ι₁
  ι₂_smooth : MDifferentiable I I ι₂
  symp₁ : ManifoldSymplecticForm I M₁
  symp₂ : ManifoldSymplecticForm I M₂
  sympQ : ManifoldSymplecticForm I Q
  codim_two₁ : sympQ.halfDim + 1 = symp₁.halfDim
  codim_two₂ : sympQ.halfDim + 1 = symp₂.halfDim
  normalBundleTriv₁ : ∃ (U₁ : Set M₁) (φ₁ : U₁ → Q × (Fin 2 → ℝ)),
    Function.Bijective φ₁ ∧

    (∀ q : Q, ∃ h : ι₁ q ∈ U₁, φ₁ ⟨ι₁ q, h⟩ = (q, 0))
  normalBundleTriv₂ : ∃ (U₂ : Set M₂) (φ₂ : U₂ → Q × (Fin 2 → ℝ)),
    Function.Bijective φ₂ ∧
    (∀ q : Q, ∃ h : ι₂ q ∈ U₂, φ₂ ⟨ι₂ q, h⟩ = (q, 0))

/-- **Symplectic sum existence (manifold formulation).**

Given symplectic fiber-sum data $(M_1, M_2, Q)$ in the manifold-with-corners
formalism, there exists a smooth manifold $R$ carrying a symplectic form whose
half-dimension matches that of $M_1$. -/
structure LefschetzPencil.Mfld
    {E₄ : Type*} [NormedAddCommGroup E₄] [NormedSpace ℝ E₄]
    {H₄ : Type*} [TopologicalSpace H₄]
    (I₄ : ModelWithCorners ℝ E₄ H₄)
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {H₂ : Type*} [TopologicalSpace H₂]
    (I₂ : ModelWithCorners ℝ E₂ H₂)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H₄ M] [IsManifold I₄ ⊤ M]
    (B₂ : Type*) [TopologicalSpace B₂] [ChartedSpace H₂ B₂] [IsManifold I₂ ⊤ B₂]
    where
  f : M → B₂
  numCriticalPoints : ℕ
  criticalPoints : Fin numCriticalPoints → M
  smooth_away : ∀ x : M, (∀ i, x ≠ criticalPoints i) →
    MDifferentiableAt I₄ I₂ f x
  deriv_zero_at_crit : ∀ i : Fin numCriticalPoints,
    mfderiv I₄ I₂ f (criticalPoints i) = 0
  hessian_nondegenerate : ∀ x : M, (∀ i, x ≠ criticalPoints i) →
    Function.Surjective (mfderiv I₄ I₂ f x)
  generic_fiber_nonempty : ∃ (b : B₂),
    (∀ i, f (criticalPoints i) ≠ b) ∧
    Set.Nonempty (f ⁻¹' {b})

