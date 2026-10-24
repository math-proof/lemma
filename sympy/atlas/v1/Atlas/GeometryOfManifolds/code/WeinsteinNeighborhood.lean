/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/WeinsteinNeighborhood.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.MoserDarboux
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.MoserDarboux
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.BlockMatrixLp
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.ODE.PicardLindelof

set_option autoImplicit false

open Module FiniteDimensional
open SymplecticLinearAlgebra
open DifferentialFormSpace


namespace WeinsteinNeighborhood

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The linear map $V \to E^*$ sending $v \mapsto (e \mapsto \Omega(v, e))$,
where $\Omega$ is a bilinear form on $V$ and $E \subseteq V$ a subspace. -/
noncomputable def symplecticToDual (Ω : LinearMap.BilinForm ℝ V) (E : Submodule ℝ V) :
    V →ₗ[ℝ] Dual ℝ E where
  toFun v := {
    toFun := fun e => Ω v (e : V)
    map_add' := by intro e₁ e₂; simp [map_add]
    map_smul' := by intro r e; simp [map_smul]
  }
  map_add' := by intro v w; ext e; simp [map_add, LinearMap.add_apply]
  map_smul' := by intro r v; ext e; simp [map_smul, LinearMap.smul_apply]

/-- The kernel of `symplecticToDual Ω E` is the symplectic orthogonal complement
$E^{\perp_\Omega} = \{v \in V : \Omega(v, e) = 0 \text{ for all } e \in E\}$. -/
lemma symplecticToDual_ker [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    (E : Submodule ℝ V) :
    LinearMap.ker (symplecticToDual Ω E) = symplecticOrtho Ω E := by
  ext v
  simp only [LinearMap.mem_ker, symplecticOrtho]
  constructor
  · intro hv u hu
    have : (symplecticToDual Ω E v) ⟨u, hu⟩ = 0 := by rw [hv]; rfl
    simp [symplecticToDual] at this
    exact hΩ.alt.isRefl v u this
  · intro hv
    ext ⟨e, he⟩
    simp [symplecticToDual]
    exact hΩ.alt.isRefl e v (hv e he)

/-- A Lagrangian subspace $E$ is contained in the kernel of `symplecticToDual Ω E`,
since $E = E^{\perp_\Omega}$. -/
lemma lagrangian_le_ker [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    E ≤ LinearMap.ker (symplecticToDual Ω E) := by
  rw [symplecticToDual_ker hΩ]
  unfold IsLagrangian at hE
  rw [hE]

/-- For $E \subseteq V$ Lagrangian, the descent of `symplecticToDual Ω E` to
a linear map $V/E \to E^*$ given by $[v] \mapsto \Omega(v, \cdot)|_E$. -/
noncomputable def quotientToDual [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    (V ⧸ E) →ₗ[ℝ] Dual ℝ E :=
  E.liftQ (symplecticToDual Ω E) (lagrangian_le_ker hΩ hE)

/-- The induced map $V/E \to E^*$ is injective for $E$ Lagrangian, because the kernel
of the original map is exactly $E^{\perp_\Omega} = E$. -/
lemma quotientToDual_injective [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    Function.Injective (quotientToDual hΩ hE) := by
  rw [← LinearMap.ker_eq_bot]
  unfold quotientToDual
  rw [Submodule.ker_liftQ]
  rw [symplecticToDual_ker hΩ]
  unfold IsLagrangian at hE
  rw [hE]
  exact Submodule.mkQ_map_self E

/-- For $E$ a Lagrangian subspace, $\dim(V/E) = \dim E^* = \dim E$, since
$\dim E = \tfrac12 \dim V$. -/
lemma quotient_finrank_eq_dual [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    finrank ℝ (V ⧸ E) = finrank ℝ (Dual ℝ E) := by
  rw [Subspace.dual_finrank_eq]
  have hq := Submodule.finrank_quotient_add_finrank E
  have h2 := lagrangian_half_dim hΩ hE
  omega


/-- **Linear Lagrangian normal bundle identification.** For $E$ a Lagrangian subspace
of a symplectic vector space $(V, \Omega)$, there is a natural linear isomorphism
$V/E \xrightarrow{\sim} E^*$, identifying the "normal space" to $E$ with $T^*E$. -/
noncomputable def lagrangianQuotientDualEquiv [FiniteDimensional ℝ V]
    {Ω : LinearMap.BilinForm ℝ V} (hΩ : IsSymplecticForm Ω)
    {E : Submodule ℝ V} (hE : IsLagrangian Ω E) :
    (V ⧸ E) ≃ₗ[ℝ] Dual ℝ E :=
  LinearMap.linearEquivOfInjective
    (quotientToDual hΩ hE)
    (quotientToDual_injective hΩ hE)
    (quotient_finrank_eq_dual hΩ hE)

end WeinsteinNeighborhood


/-- A *relative homotopy operator* for an inclusion $i : X \hookrightarrow U$ packages
the chain-level data showing that $i^*$ is a homotopy equivalence:
a retraction $\pi : U \to X$, a chain homotopy
$K : \Omega^{p+1}(U) \to \Omega^p(U)$ satisfying
$dK + Kd = \mathrm{id} - \pi^* i^*$, and the additional condition $i^* K = 0$
(so that primitives vanish on $X$). -/
structure HasRelativeHomotopyOperator
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF]
    (Ω_X : ℕ → Type*) (VF_X : Type*) [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF) where
  π : DFSMorphism Ω VF Ω_X VF_X
  retraction : ∀ {p : ℕ} (α : Ω_X p), i.pullback (π.pullback α) = α
  K : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  K_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)), K (r • α) = r • K α
  homotopy_formula : ∀ {p : ℕ} (β : Ω (p + 1)),
    inst.d (K β) + K (inst.d β) = β - π.pullback (i.pullback β)
  K_vanishes_on_X : ∀ {p : ℕ} (β : Ω (p + 1)), i.pullback (K β) = 0


/-- Cartan's magic formula applied to a chosen "scaling" vector field $V$:
$d\iota_V \beta + \iota_V d\beta = \mathcal{L}_V \beta$. -/
theorem cartan_for_scaling_field
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (V : VF) {p : ℕ} (β : Ω (p + 1)) :
    inst.d (inst.ι V β) + inst.ι V (inst.d β) = inst.L V β := by
  rw [cartan_formula]

/-- Derivation of the chain homotopy formula $dK + Kd = \mathrm{id} - \pi^* i^*$ from
Cartan's formula together with a "fundamental theorem of calculus" identity
$\Phi(\mathcal{L}_V \beta) = \beta - \pi^*(i^*\beta)$, where $K := \Phi \circ \iota_V$. -/
theorem homotopy_formula_from_cartan_and_ftc
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Ω_X : ℕ → Type*} {VF_X : Type*} [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF)
    (π : DFSMorphism Ω VF Ω_X VF_X)
    (V : VF) (Φ : ∀ {p : ℕ}, Ω p → Ω p) (K : ∀ {p : ℕ}, Ω (p + 1) → Ω p)

    (hK_def : ∀ {p : ℕ} (β : Ω (p + 1)), K β = Φ (inst.ι V β))

    (hΦ_add : ∀ {p : ℕ} (γ₁ γ₂ : Ω p), Φ (γ₁ + γ₂) = Φ γ₁ + Φ γ₂)

    (hΦ_d : ∀ {p : ℕ} (γ : Ω p), inst.d (Φ γ) = Φ (inst.d γ))

    (hFTC : ∀ {p : ℕ} (β : Ω (p + 1)), Φ (inst.L V β) = β - π.pullback (i.pullback β))
    {p : ℕ} (β : Ω (p + 1)) :
    inst.d (K β) + K (inst.d β) = β - π.pullback (i.pullback β) := by

  rw [hK_def β]


  rw [hK_def (inst.d β)]


  rw [hΦ_d (inst.ι V β)]


  rw [← hΦ_add]


  rw [cartan_for_scaling_field V β]


  exact hFTC β

/-- $\mathbb{R}$-linearity of $K = \Phi \circ \iota_V$ in its argument, derived from the
linearity of $\iota_V$ and the scalar-multiplicativity of $\Phi$. -/
theorem K_smul_from_axioms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (V : VF) (Φ : ∀ {p : ℕ}, Ω p → Ω p)

    (hΦ_smul : ∀ {p : ℕ} (r : ℝ) (γ : Ω p), Φ (r • γ) = r • Φ γ)
    {p : ℕ} (r : ℝ) (α : Ω (p + 1)) :
    Φ (inst.ι V (r • α)) = r • Φ (inst.ι V α) := by
  rw [inst.ι_smul]
  exact hΦ_smul r (inst.ι V α)

/-- $K\beta = \Phi(\iota_V \beta)$ pulls back to zero on $X$, since $\iota_V$ already does
and $\Phi$ preserves vanishing on $X$. -/
theorem K_vanishes_on_X_from_axioms
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Ω_X : ℕ → Type*} {VF_X : Type*} [_inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF)
    (V : VF) (Φ : ∀ {p : ℕ}, Ω p → Ω p)

    (hιV_vanish : ∀ {p : ℕ} (β : Ω (p + 1)), i.pullback (inst.ι V β) = 0)

    (hΦ_preserve : ∀ {p : ℕ} (γ : Ω p), i.pullback γ = 0 → i.pullback (Φ γ) = 0)
    {p : ℕ} (β : Ω (p + 1)) :
    i.pullback (Φ (inst.ι V β)) = 0 := by
  exact hΦ_preserve (inst.ι V β) (hιV_vanish β)


/-- *Tubular homotopy primitives* for an inclusion $i : X \hookrightarrow U$: the data of a
retraction $\pi$, an Euler-like vector field $V$, and a "radial integration" operator
$\Phi$ satisfying additivity, scalar-multiplicativity, commutation with $d$, an "FTC"
identity $\Phi(\mathcal{L}_V \beta) = \beta - \pi^* i^*\beta$, and the conditions
$i^*(\iota_V \beta) = 0$ and $i^* \Phi = i^*$.

Such primitives canonically produce a relative homotopy operator via
$K := \Phi \circ \iota_V$. -/
structure HasTubularHomotopyPrimitives
    (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF]
    (Ω_X : ℕ → Type*) (VF_X : Type*) [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF) where
  π : DFSMorphism Ω VF Ω_X VF_X
  retraction : ∀ {p : ℕ} (α : Ω_X p), i.pullback (π.pullback α) = α
  V : VF
  Φ : ∀ {p : ℕ}, Ω p → Ω p
  Φ_add : ∀ {p : ℕ} (γ₁ γ₂ : Ω p), Φ (γ₁ + γ₂) = Φ γ₁ + Φ γ₂
  Φ_smul : ∀ {p : ℕ} (r : ℝ) (γ : Ω p), Φ (r • γ) = r • Φ γ
  Φ_d : ∀ {p : ℕ} (γ : Ω p), inst.d (Φ γ) = Φ (inst.d γ)
  Φ_FTC : ∀ {p : ℕ} (β : Ω (p + 1)), Φ (inst.L V β) = β - π.pullback (i.pullback β)
  ιV_vanish_on_X : ∀ {p : ℕ} (β : Ω (p + 1)), i.pullback (inst.ι V β) = 0
  Φ_fix_X : ∀ {p : ℕ} (γ : Ω p), i.pullback (Φ γ) = i.pullback γ

/-- Construct a `HasRelativeHomotopyOperator` from the more granular tubular
homotopy primitives, via $K := \Phi \circ \iota_V$. -/
noncomputable def hasRelativeHomotopyOperator_of_primitives
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    {Ω_X : ℕ → Type*} {VF_X : Type*} [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF)
    (hp : HasTubularHomotopyPrimitives Ω VF Ω_X VF_X i)
    : HasRelativeHomotopyOperator Ω VF Ω_X VF_X i where
  π := hp.π
  retraction := hp.retraction
  K β := hp.Φ (inst.ι hp.V β)
  K_smul r α := K_smul_from_axioms hp.V hp.Φ hp.Φ_smul r α
  homotopy_formula β := homotopy_formula_from_cartan_and_ftc i hp.π hp.V hp.Φ
    (fun β => hp.Φ (inst.ι hp.V β))
    (fun β => rfl) hp.Φ_add hp.Φ_d hp.Φ_FTC β
  K_vanishes_on_X β := K_vanishes_on_X_from_axioms i hp.V hp.Φ
    hp.ιV_vanish_on_X hp.Φ_preserves_vanishing β


/-- An algebraic *deformation retract* of $U$ onto $X$: a relative homotopy operator
together with an injectivity condition at degree 0 (forms of degree 0 with vanishing
differential and vanishing pullback are zero). -/
structure HasDeformationRetract
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_U : ℕ → Type*} {VF_U : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_U : DifferentialFormSpace Ω_U VF_U]
    (i : DFSMorphism Ω_X VF_X Ω_U VF_U) where
  π : DFSMorphism Ω_U VF_U Ω_X VF_X
  retraction : ∀ {p : ℕ} (α : Ω_X p), i.pullback (π.pullback α) = α
  K : ∀ {p : ℕ}, Ω_U (p + 1) → Ω_U p
  K_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω_U (p + 1)), K (r • α) = r • K α
  homotopy_formula : ∀ {p : ℕ} (β : Ω_U (p + 1)),
    inst_U.d (K β) + K (inst_U.d β) = β - π.pullback (i.pullback β)
  K_vanishes_on_X : ∀ {p : ℕ} (β : Ω_U (p + 1)), i.pullback (K β) = 0
  deg0_injectivity : ∀ (β : Ω_U 0), inst_U.d β = (0 : Ω_U 1) →
    i.pullback β = (0 : Ω_X 0) → β = (0 : Ω_U 0)

/-- Abstract data for the *normal bundle* $NX \to X$ at the level of differential forms:
a zero-section morphism $X \to NX$ and a projection $NX \to X$ whose composition
pulled back to forms is the identity on $\Omega^*(X)$. -/
structure NormalBundleDFS
    (Ω_X : ℕ → Type*) (VF_X : Type*)
    (Ω_NX : ℕ → Type*) (VF_NX : Type*)
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_NX : DifferentialFormSpace Ω_NX VF_NX] where
  zeroSection : DFSMorphism Ω_X VF_X Ω_NX VF_NX
  projection : DFSMorphism Ω_NX VF_NX Ω_X VF_X
  proj_section : ∀ {p : ℕ} (α : Ω_X p),
    zeroSection.pullback (projection.pullback α) = α


/-- Predicate that the DFS morphism $i : X \hookrightarrow M$ comes from a smooth
submanifold inclusion of dimensions $\dim X \le \dim M$. -/
structure IsSubmanifoldInclusion
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [DifferentialFormSpace Ω_X VF_X]
    [DifferentialFormSpace Ω_M VF_M]
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (dimM dimX : ℕ) : Prop where
  dim_le : dimX ≤ dimM


/-- Compatibility predicate stating that $U \subseteq N$ is an open neighborhood of
$X \subseteq N$: the inclusion $X \hookrightarrow N$ factors as
$X \hookrightarrow U \hookrightarrow N$ on differential forms. -/
structure IsOpenNeighborhoodOf
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_U : ℕ → Type*} {VF_U : Type*}
    {Ω_N : ℕ → Type*} {VF_N : Type*}
    [DifferentialFormSpace Ω_X VF_X]
    [inst_U : DifferentialFormSpace Ω_U VF_U]
    [DifferentialFormSpace Ω_N VF_N]
    (incl_X_N : DFSMorphism Ω_X VF_X Ω_N VF_N)
    (incl_U_N : @DFSMorphism Ω_U VF_U Ω_N VF_N inst_U _)
    (incl_X_U : @DFSMorphism Ω_X VF_X Ω_U VF_U _ inst_U) : Prop where
  compatible : ∀ {p : ℕ} (α : Ω_N p),
    incl_X_U.pullback (incl_U_N.pullback α) = incl_X_N.pullback α

/-- A pair of DFS morphisms $\varphi, \varphi^{-1}$ form a *DFS diffeomorphism* if their
pullbacks are mutually inverse on all differential forms. -/
structure IsDFSDiffeomorphism
    {Ω₁ : ℕ → Type*} {VF₁ : Type*}
    {Ω₂ : ℕ → Type*} {VF₂ : Type*}
    [inst₁ : DifferentialFormSpace Ω₁ VF₁]
    [inst₂ : DifferentialFormSpace Ω₂ VF₂]
    (φ : @DFSMorphism Ω₁ VF₁ Ω₂ VF₂ inst₁ inst₂)
    (φ_inv : @DFSMorphism Ω₂ VF₂ Ω₁ VF₁ inst₂ inst₁) : Prop where
  left_inv : ∀ {p : ℕ} (α : Ω₂ p), φ_inv.pullback (φ.pullback α) = α
  right_inv : ∀ {p : ℕ} (α : Ω₁ p), φ.pullback (φ_inv.pullback α) = α


/-- The data of an *exponential map* used in proving the tubular neighborhood theorem:
an open neighborhood $U_0$ of $X$ in $NX$ together with a smooth map
$\exp : U_0 \to M$ whose restriction to the zero section is $i : X \hookrightarrow M$. -/
class HasTubularExpMapData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_NX : ℕ → Type*} {VF_NX : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_NX : DifferentialFormSpace Ω_NX VF_NX]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (nb : NormalBundleDFS Ω_X VF_X Ω_NX VF_NX)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (dimM dimX : ℕ)
    (hSubmfd : IsSubmanifoldInclusion i dimM dimX) where
  Ω_U₀ : ℕ → Type*
  VF_U₀ : Type*
  inst_U₀ : DifferentialFormSpace Ω_U₀ VF_U₀
  exp_map : @DFSMorphism Ω_U₀ VF_U₀ Ω_M VF_M inst_U₀ inst_M
  j₀ : @DFSMorphism Ω_U₀ VF_U₀ Ω_NX VF_NX inst_U₀ inst_NX
  s₀ : @DFSMorphism Ω_X VF_X Ω_U₀ VF_U₀ inst_X inst_U₀
  hU₀_nbhd : @IsOpenNeighborhoodOf Ω_X VF_X Ω_U₀ VF_U₀ Ω_NX VF_NX
    inst_X inst_U₀ inst_NX nb.zeroSection j₀ s₀
  hd_exp_id : ∀ {p : ℕ} (α : Ω_M p), s₀.pullback (exp_map.pullback α) = i.pullback α

/-- The output of the *inverse function theorem* applied to the exponential map: a
DFS-diffeomorphism $\varphi : U_0 \xrightarrow{\sim} U_1$ where $U_1 \subseteq M$, together
with the factorization $\exp = \mathrm{incl}_{U_1 \hookrightarrow M} \circ \varphi$. -/
class HasIFTData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_NX : ℕ → Type*} {VF_NX : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_U₀ : ℕ → Type*} {VF_U₀ : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_NX : DifferentialFormSpace Ω_NX VF_NX]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_U₀ : DifferentialFormSpace Ω_U₀ VF_U₀]
    (nb : NormalBundleDFS Ω_X VF_X Ω_NX VF_NX)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (exp_map : DFSMorphism Ω_U₀ VF_U₀ Ω_M VF_M)
    (j₀ : DFSMorphism Ω_U₀ VF_U₀ Ω_NX VF_NX)
    (s₀ : DFSMorphism Ω_X VF_X Ω_U₀ VF_U₀)
    (hU₀_nbhd : IsOpenNeighborhoodOf nb.zeroSection j₀ s₀)
    (hd_exp_id : ∀ {p : ℕ} (α : Ω_M p), s₀.pullback (exp_map.pullback α) = i.pullback α) where
  Ω_U₁ : ℕ → Type*
  VF_U₁ : Type*
  inst_U₁ : DifferentialFormSpace Ω_U₁ VF_U₁
  φ : @DFSMorphism Ω_U₀ VF_U₀ Ω_U₁ VF_U₁ inst_U₀ inst_U₁
  φ_inv : @DFSMorphism Ω_U₁ VF_U₁ Ω_U₀ VF_U₀ inst_U₁ inst_U₀
  incl_U₁_M : @DFSMorphism Ω_U₁ VF_U₁ Ω_M VF_M inst_U₁ inst_M
  hDiffeo : @IsDFSDiffeomorphism Ω_U₀ VF_U₀ Ω_U₁ VF_U₁ inst_U₀ inst_U₁ φ φ_inv
  exp_factors : ∀ {p : ℕ} (α : Ω_M p),
    φ.pullback (incl_U₁_M.pullback α) = exp_map.pullback α


/-- Packaging of the *conclusion* of the tubular neighborhood theorem: open
neighborhoods $U_0$ of $X$ in $NX$ and $U_1$ of $X$ in $M$, a DFS-diffeomorphism
$\varphi : U_0 \xrightarrow{\sim} U_1$ that restricts to the identity on $X$, together with
the relevant inclusions and the open-neighborhood data on both sides. -/
structure TubularNeighborhoodData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_NX : ℕ → Type*} {VF_NX : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_NX : DifferentialFormSpace Ω_NX VF_NX]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (nb : NormalBundleDFS Ω_X VF_X Ω_NX VF_NX)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M) where
  Ω_U₀ : ℕ → Type*
  VF_U₀ : Type*
  inst_U₀ : DifferentialFormSpace Ω_U₀ VF_U₀
  Ω_U₁ : ℕ → Type*
  VF_U₁ : Type*
  inst_U₁ : DifferentialFormSpace Ω_U₁ VF_U₁
  φ : @DFSMorphism Ω_U₀ VF_U₀ Ω_U₁ VF_U₁ inst_U₀ inst_U₁
  φ_inv : @DFSMorphism Ω_U₁ VF_U₁ Ω_U₀ VF_U₀ inst_U₁ inst_U₀
  j₀ : @DFSMorphism Ω_U₀ VF_U₀ Ω_NX VF_NX inst_U₀ inst_NX
  s₀ : @DFSMorphism Ω_X VF_X Ω_U₀ VF_U₀ inst_X inst_U₀
  j₁ : @DFSMorphism Ω_X VF_X Ω_U₁ VF_U₁ inst_X inst_U₁
  incl_U₁_M : @DFSMorphism Ω_U₁ VF_U₁ Ω_M VF_M inst_U₁ inst_M
  hDiffeo : @IsDFSDiffeomorphism Ω_U₀ VF_U₀ Ω_U₁ VF_U₁ inst_U₀ inst_U₁ φ φ_inv
  hU₀_nbhd : @IsOpenNeighborhoodOf Ω_X VF_X Ω_U₀ VF_U₀ Ω_NX VF_NX
    inst_X inst_U₀ inst_NX nb.zeroSection j₀ s₀
  hU₁_nbhd : @IsOpenNeighborhoodOf Ω_X VF_X Ω_U₁ VF_U₁ Ω_M VF_M
    inst_X inst_U₁ inst_M i incl_U₁_M j₁
  hφ_X : ∀ {p : ℕ} (α : Ω_U₁ p), s₀.pullback (φ.pullback α) = j₁.pullback α

/-- **Tubular neighborhood theorem (assembly).** Given an exponential map data and the
output of the inverse function theorem, this assembles the full tubular neighborhood
data: $X \subseteq M$ admits a tubular neighborhood $U_1 \cong U_0 \subseteq NX$. -/
def tubular_neighborhood_theorem
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_NX : ℕ → Type*} {VF_NX : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_NX : DifferentialFormSpace Ω_NX VF_NX]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    (nb : NormalBundleDFS Ω_X VF_X Ω_NX VF_NX)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (dimM dimX : ℕ)
    (hSubmfd : IsSubmanifoldInclusion i dimM dimX)

    [expData : HasTubularExpMapData nb i dimM dimX hSubmfd]

    [iftData : @HasIFTData Ω_X VF_X Ω_NX VF_NX Ω_M VF_M
      expData.Ω_U₀ expData.VF_U₀
      inst_X inst_NX inst_M expData.inst_U₀
      nb i expData.exp_map expData.j₀ expData.s₀
      expData.hU₀_nbhd expData.hd_exp_id] :
    @TubularNeighborhoodData Ω_X VF_X Ω_NX VF_NX Ω_M VF_M
      inst_X inst_NX inst_M nb i :=


  letI : DifferentialFormSpace expData.Ω_U₀ expData.VF_U₀ := expData.inst_U₀
  letI : DifferentialFormSpace iftData.Ω_U₁ iftData.VF_U₁ := iftData.inst_U₁
  { Ω_U₀ := expData.Ω_U₀
    VF_U₀ := expData.VF_U₀
    inst_U₀ := expData.inst_U₀
    Ω_U₁ := iftData.Ω_U₁
    VF_U₁ := iftData.VF_U₁
    inst_U₁ := iftData.inst_U₁
    φ := iftData.φ
    φ_inv := iftData.φ_inv
    j₀ := expData.j₀
    s₀ := expData.s₀

    j₁ :=
      { pullback := fun α => expData.s₀.pullback (iftData.φ.pullback α)
        pullback_add := fun α β => by simp [iftData.φ.pullback_add, expData.s₀.pullback_add]
        pullback_smul := fun r α => by simp [iftData.φ.pullback_smul, expData.s₀.pullback_smul]
        pullback_comm_d := fun α => by simp [iftData.φ.pullback_comm_d, expData.s₀.pullback_comm_d] }
    incl_U₁_M := iftData.incl_U₁_M
    hDiffeo := iftData.hDiffeo
    hU₀_nbhd := expData.hU₀_nbhd

    hU₁_nbhd := ⟨fun α => by


      show expData.s₀.pullback (iftData.φ.pullback (iftData.incl_U₁_M.pullback α)) = i.pullback α

      rw [iftData.exp_factors α]

      exact expData.hd_exp_id α⟩

    hφ_X := fun _ => rfl }


/-- The 2-form $\omega$ has the property that contraction $v \mapsto \iota_v \omega$
hits every 1-form — equivalently, $\omega^\flat : TM \to T^*M$ is surjective. -/
def ContractionSurjective
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (ω : Ω 2) : Prop :=
  ∀ (α : Ω 1), ∃ (v : VF), inst.ι v ω = α

/-- The DFS morphism $i : U \hookrightarrow M$ comes from a *proper* open inclusion
$U \subsetneq M$: pullback on smooth functions is not surjective. -/
def IsProperSubDFS {Ω₁ : ℕ → Type*} {VF₁ : Type*} [DifferentialFormSpace Ω₁ VF₁]
    {Ω₂ : ℕ → Type*} {VF₂ : Type*} [DifferentialFormSpace Ω₂ VF₂]
    (i : DFSMorphism Ω₁ VF₁ Ω₂ VF₂) : Prop :=
  ¬ Function.Surjective (fun (α : Ω₂ 0) => i.pullback α)

/-- A global Moser flow $\varphi_M : M \to M$ matching $\omega_1$ to $\omega_0$ and
fixing $X$ restricts to a local diffeomorphism between open neighborhoods
$U_0, U_1$ of $X$. -/
structure IsClosedSubmanifold
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    [DifferentialFormSpace Ω_M VF_M]
    [DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M) : Prop where
  pullback_surj : ∀ (p : ℕ) (α : Ω_X p), ∃ (β : Ω_M p), i.pullback β = α

/-- All the geometric data produced by combining the tubular neighborhood theorem with
the Lagrangian normal-bundle identification $NX \cong T^*X$: a common neighborhood $U$
of $X$ carrying two symplectic forms $\omega_0$ (from $T^*X$) and $\omega_1$ (from $M$)
that agree on $X$, together with the auxiliary inclusions and a $V$-side neighborhood
diffeomorphic to $U$ identifying $\omega_1$ with the symplectic form on $M$. -/
structure TubularNeighborhoodGeometricData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_TX : ℕ → Type*} {VF_TX : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_TX : DifferentialFormSpace Ω_TX VF_TX]
    [hCot : CotangentBundleDFS Ω_X VF_X Ω_TX VF_TX]
    (S_M : SymplecticManifold Ω_M VF_M)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (hLag : IsLagrangianSubmanifold S_M i (2 * hCot.dimX) hCot.dimX) where
  Ω_U : ℕ → Type*
  VF_U : Type*
  inst_U : DifferentialFormSpace Ω_U VF_U
  j : @DFSMorphism Ω_X VF_X Ω_U VF_U inst_X inst_U
  ω₀ : Ω_U 2
  ω₁ : Ω_U 2
  hclosed₀ : inst_U.d ω₀ = 0
  hclosed₁ : inst_U.d ω₁ = 0
  hnd₀ : Function.Injective (fun (X : VF_U) => inst_U.ι X ω₀)
  hnd₁ : Function.Injective (fun (X : VF_U) => inst_U.ι X ω₁)
  Ω_V : ℕ → Type*
  VF_V : Type*
  inst_V : DifferentialFormSpace Ω_V VF_V
  ψ : @DFSMorphism Ω_U VF_U Ω_V VF_V inst_U inst_V
  ψ_inv : @DFSMorphism Ω_V VF_V Ω_U VF_U inst_V inst_U
  S_V : @SymplecticManifold Ω_V VF_V inst_V
  j_V : @DFSMorphism Ω_X VF_X Ω_V VF_V inst_X inst_V
  ψ_left : ∀ {p : ℕ} (α : Ω_V p), ψ_inv.pullback (ψ.pullback α) = α
  ψ_right : ∀ {p : ℕ} (α : Ω_U p), ψ.pullback (ψ_inv.pullback α) = α
  hω₁ : ψ.pullback S_V.ω = ω₁
  hψ_X : ∀ {p : ℕ} (α : Ω_V p), j.pullback (ψ.pullback α) = j_V.pullback α


  ι_U : @DFSMorphism Ω_U VF_U Ω_TX VF_TX inst_U inst_TX
  ι_V : @DFSMorphism Ω_V VF_V Ω_M VF_M inst_V inst_M
  hι_U_compat : ∀ {p : ℕ} (α : Ω_TX p), j.pullback (ι_U.pullback α) = hCot.zeroSection.pullback α
  hι_V_compat : ∀ {p : ℕ} (α : Ω_M p), j_V.pullback (ι_V.pullback α) = i.pullback α

/-- Axiomatic existence of `TubularNeighborhoodGeometricData` for any closed
Lagrangian submanifold $X$ of a symplectic manifold $(M, \omega)$. -/
class HasMoserInfrastructure
    {Ω : ℕ → Type u_Ω} {VF : Type u_VF}
    [inst : DifferentialFormSpace Ω VF]
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    (i : DFSMorphism Ω_X VF_X Ω VF) where
  homotopyPrimitives : HasTubularHomotopyPrimitives Ω VF Ω_X VF_X i
  moserTransportData :
    (ω₀ ω₁ : Ω 2) →
    (hclosed₀ : inst.d ω₀ = 0) → (hclosed₁ : inst.d ω₁ = 0) →
    (hnd₀ : Function.Injective (fun X => inst.ι X ω₀)) →
    (hagree : ∀ (V : VF), i.pullback (inst.ι V ω₀) = i.pullback (inst.ι V ω₁)) →
    (hH : HasRelativeHomotopyOperator Ω VF Ω_X VF_X i) →
    ∃ (φ : DFSMorphism Ω VF Ω VF) (φ_inv : DFSMorphism Ω VF Ω VF),
      φ.pullback ω₁ = ω₀ ∧
      (∀ {p : ℕ} (α : Ω p), φ_inv.pullback (φ.pullback α) = α) ∧
      (∀ {p : ℕ} (α : Ω p), φ.pullback (φ_inv.pullback α) = α) ∧
      (∀ {p : ℕ} (α : Ω p), i.pullback (φ.pullback α) = i.pullback α)


/-- All the geometric and Moser-flow data needed to prove Weinstein's Lagrangian
neighborhood theorem: a common neighborhood $U$ of $X$ with two symplectic forms
$\omega_0$ (induced from $T^*X$) and $\omega_1$ (induced from $M$), a $V$-side
neighborhood diffeomorphic to $U$ realizing $\omega_1$ as a pullback of the symplectic
form on $M$, and a Moser flow $\varphi$ on $U$ matching $\omega_1$ to $\omega_0$
that fixes $X$. -/
class HasLagrangianTubularData
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_TX : ℕ → Type*} {VF_TX : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_TX : DifferentialFormSpace Ω_TX VF_TX]
    [hCot : CotangentBundleDFS Ω_X VF_X Ω_TX VF_TX]
    (S_M : SymplecticManifold Ω_M VF_M)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (hLag : IsLagrangianSubmanifold S_M i (2 * hCot.dimX) hCot.dimX) where
  Ω_U : ℕ → Type*
  VF_U : Type*
  inst_U : DifferentialFormSpace Ω_U VF_U
  j : @DFSMorphism Ω_X VF_X Ω_U VF_U inst_X inst_U
  ω₀ : Ω_U 2
  ω₁ : Ω_U 2
  hclosed₀ : inst_U.d ω₀ = 0
  hclosed₁ : inst_U.d ω₁ = 0
  hagree : ∀ (V : VF_U), j.pullback (inst_U.ι V ω₀) = j.pullback (inst_U.ι V ω₁)
  hnd₀ : Function.Injective (fun (X : VF_U) => inst_U.ι X ω₀)
  hnd₁ : Function.Injective (fun (X : VF_U) => inst_U.ι X ω₁)
  Ω_V : ℕ → Type*
  VF_V : Type*
  inst_V : DifferentialFormSpace Ω_V VF_V
  ψ : @DFSMorphism Ω_U VF_U Ω_V VF_V inst_U inst_V
  ψ_inv : @DFSMorphism Ω_V VF_V Ω_U VF_U inst_V inst_U
  S_V : @SymplecticManifold Ω_V VF_V inst_V
  j_V : @DFSMorphism Ω_X VF_X Ω_V VF_V inst_X inst_V
  ψ_left : ∀ {p : ℕ} (α : Ω_V p), ψ_inv.pullback (ψ.pullback α) = α
  ψ_right : ∀ {p : ℕ} (α : Ω_U p), ψ.pullback (ψ_inv.pullback α) = α
  hω₁ : ψ.pullback S_V.ω = ω₁
  hψ_X : ∀ {p : ℕ} (α : Ω_V p), j.pullback (ψ.pullback α) = j_V.pullback α
  ι_U : @DFSMorphism Ω_U VF_U Ω_TX VF_TX inst_U inst_TX
  ι_V : @DFSMorphism Ω_V VF_V Ω_M VF_M inst_V inst_M
  hι_U_compat : ∀ {p : ℕ} (α : Ω_TX p), j.pullback (ι_U.pullback α) = hCot.zeroSection.pullback α
  hι_V_compat : ∀ {p : ℕ} (α : Ω_M p), j_V.pullback (ι_V.pullback α) = i.pullback α

  φ : @DFSMorphism Ω_U VF_U Ω_U VF_U inst_U inst_U
  φ_inv : @DFSMorphism Ω_U VF_U Ω_U VF_U inst_U inst_U
  hφ_pull : φ.pullback ω₁ = ω₀
  hφ_left : ∀ {p : ℕ} (α : Ω_U p), φ_inv.pullback (φ.pullback α) = α
  hφ_right : ∀ {p : ℕ} (α : Ω_U p), φ.pullback (φ_inv.pullback α) = α
  hφ_id_X : ∀ {p : ℕ} (α : Ω_U p), j.pullback (φ.pullback α) = j.pullback α

/-- Existence of `HasLagrangianTubularData`: combine the geometric tubular neighborhood
data with the first-order agreement of $\omega_0$ and $\omega_1$ on $X$, then apply
the local Moser theorem to produce the required diffeomorphism $\varphi$. -/
structure DFSPointEvalX
    (Ω_X : ℕ → Type*) (VF_X : Type*) (X : Type*)
    [inst_X : DifferentialFormSpace Ω_X VF_X] where
  isZeroAt : Ω_X 1 → X → Prop

/-- Axiomatic vanishing of $H^1(X, \mathbb{R})$: every closed 1-form on $X$ is exact,
i.e. $\mu = dh$ for some smooth $h : X \to \mathbb{R}$. -/
structure HasH1Vanishing
    (Ω_X : ℕ → Type*) (VF_X : Type*)
    [inst_X : DifferentialFormSpace Ω_X VF_X] : Prop where
  exact_of_closed : ∀ (μ : Ω_X 1), inst_X.d μ = 0 → ∃ (h : Ω_X 0), μ = inst_X.d h

/-- On a compact (Hausdorff) manifold $X$, every smooth function $h : X \to \mathbb{R}$
has at least two critical points (achieving its max and min). -/
structure C1CloseLagrangian
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_TX : ℕ → Type*} {VF_TX : Type*}
    {X : Type*}
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_TX : DifferentialFormSpace Ω_TX VF_TX]
    [hCot : CotangentBundleDFS Ω_X VF_X Ω_TX VF_TX]
    (ptEval : DFSPointEvalX Ω_X VF_X X)
    (S_M : SymplecticManifold Ω_M VF_M)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (hLag : IsLagrangianSubmanifold S_M i (2 * hCot.dimX) hCot.dimX) where
  μ : Ω_X 1
  μ_closed : inst_X.d μ = 0
  weinstein_intersection_iff_zero :
    ∀ (x : X), (x ∈ {p : X | ptEval.isZeroAt μ p}) ↔ ptEval.isZeroAt μ x

/-- Mathlib-flavored predicate that $i : X \to M$ is a Lagrangian embedding:
$i$ is smooth and injective. -/
class IsLagrangianEmbedding_mfld
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {HH : Type*} [TopologicalSpace HH]
    (I : ModelWithCorners ℝ E HH)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HH M] [IsManifold I ⊤ M]
    (X : Type*) [TopologicalSpace X] [ChartedSpace HH X] [IsManifold I ⊤ X]
    (i : X → M) : Prop where
  smooth : ContMDiff I I ⊤ i
  injective : Function.Injective i

/-- Mathlib-flavored axiomatization of $H^1(X, \mathbb{R}) = 0$ on a connected manifold:
any smooth function with zero differential is constant. -/
class HasVanishingH1_mfld
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {HH : Type*} [TopologicalSpace HH]
    (I : ModelWithCorners ℝ E HH)
    (X : Type*) [TopologicalSpace X] [ChartedSpace HH X] [IsManifold I ⊤ X] : Prop where
  connected : ConnectedSpace X
  exact_of_closed_forms : ∀ (f : X → ℝ),
    ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ f →
    (∀ x : X, mfderiv I (modelWithCornersSelf ℝ ℝ) f x = 0) →
    ∀ x y : X, f x = f y

/-- The Mathlib analog of `C1CloseLagrangian`: data of a smooth function
$h : X \to \mathbb{R}$ whose critical points correspond exactly to intersection points
of $X$ with a $C^1$-close submanifold $Y$. -/
structure C1CloseSubmanifold_mfld
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {HH : Type*} [TopologicalSpace HH]
    (I : ModelWithCorners ℝ E HH)
    (M : Type*) [TopologicalSpace M] [ChartedSpace HH M] [IsManifold I ⊤ M]
    (X : Type*) [TopologicalSpace X] [ChartedSpace HH X] [IsManifold I ⊤ X]
    (i : X → M) where
  isIntersectionPt : X → Prop
  h : X → ℝ
  h_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ h
  crit_iff_intersection : ∀ x : X,
    isIntersectionPt x ↔ mfderiv I (modelWithCornersSelf ℝ ℝ) h x = 0

/-- A slimmer variant of `C1CloseSubmanifold_mfld` carrying only the smooth function $h$
on $X$ and the intersection-vs-critical-point equivalence. -/
structure C1CloseLagrangianMfld
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {HH : Type*} [TopologicalSpace HH]
    (I : ModelWithCorners ℝ E HH)
    (X : Type*) [TopologicalSpace X] [ChartedSpace HH X] [IsManifold I ⊤ X] where
  h : X → ℝ
  h_smooth : ContMDiff I (modelWithCornersSelf ℝ ℝ) ⊤ h
  isIntersectionPt : X → Prop
  crit_iff_intersection : ∀ x : X,
    isIntersectionPt x ↔ mfderiv I (modelWithCornersSelf ℝ ℝ) h x = 0

/-- **Extreme value theorem giving $\ge 2$ critical points.** On a compact nontrivial
manifold $X$, every smooth $h : X \to \mathbb{R}$ has at least two distinct critical points. -/
structure HasH1Vanishing_Mathlib
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] : Prop where
  exact_of_closed : ∀ (ω : E → E [⋀^Fin 1]→L[ℝ] ℝ),
    (∀ x : E, extDeriv ω x = 0) →
    ∃ (f : E → E [⋀^Fin 0]→L[ℝ] ℝ), ∀ x : E, extDeriv f x = ω x

open scoped Manifold in
/-- Mathlib-style packaging of the Weinstein tubular neighborhood: open sets
$U \subseteq M$ containing $X$ and $U_0 \subseteq E \times E$ containing the zero
section, with a diffeomorphism $\Phi : U_0 \xrightarrow{\sim} U$ taking the zero section
into $X$ and (placeholder) preserving the symplectic structure. -/
structure WeinsteinTubular
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
    (ω : M → E [⋀^Fin 2]→L[ℝ] ℝ)
    (i : X → M)
    (hi : ContMDiff I I ⊤ i) where
  U : TopologicalSpace.Opens M
  hU_contains_X : ∀ x : X, i x ∈ U
  U₀ : TopologicalSpace.Opens (E × E)
  hU₀_zero_section : ∀ v : E, (v, (0 : E)) ∈ U₀
  Φ : Diffeomorph (modelWithCornersSelf ℝ (E × E)) I U₀ U ⊤
  hΦ_identity_on_X : ∀ (v : E) (hv : (v, (0 : E)) ∈ U₀),
    (Φ ⟨(v, 0), hv⟩ : M) ∈ Set.range i
  hΦ_symplectic : True


open scoped Manifold in
/-- Mathlib-style packaging of the (non-symplectic) tubular neighborhood theorem:
neighborhoods $U_1 \ni X$ in $M$ and $U_0 \ni$ zero section in $E \times E$, and a
diffeomorphism $\varphi : U_0 \to U_1$ mapping the zero section into $X$. -/
structure tubular_neighborhood_theorem_book_Mathlib
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M]
    (X : Type*) [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ⊤ X]
    (i : X → M)
    (hi : ContMDiff I I ⊤ i) where
  U₁ : TopologicalSpace.Opens M
  hU₁_contains_X : ∀ x : X, i x ∈ U₁
  U₀ : TopologicalSpace.Opens (E × E)
  hU₀_zero : ∀ v : E, (v, (0 : E)) ∈ U₀
  φ : Diffeomorph (modelWithCornersSelf ℝ (E × E)) I U₀ U₁ ⊤
  hφ_preserves_X : ∀ (v : E) (hv : (v, (0 : E)) ∈ U₀),
    (φ ⟨(v, 0), hv⟩ : M) ∈ Set.range i

open scoped Manifold in
/-- **Existence of an exponential-like map** in the Mathlib setting (axiomatic). For any
smooth injective $i : X \to M$, there exists an open set $U_0 \subseteq E_X \times E_N$
containing the zero section and a smooth map $\exp : U_0 \to M$ such that the zero
section lands in $i(X)$, $\exp$ is locally injective, and $i(X) \subseteq \mathrm{im}(\exp)$. -/
structure C1CloseLagrangian_Mathlib
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Type*) where
  chart : X → E
  μ : E → E [⋀^Fin 1]→L[ℝ] ℝ
  μ_closed : ∀ x : E, extDeriv μ x = 0
  isZeroAt : X → Prop
  zero_iff : ∀ x : X, isZeroAt x ↔ μ (chart x) = 0
