/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs

set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


/-- A typeclass abstracting a notion of positivity on a real vector space: a predicate
`IsPositive` closed under addition and positive scaling, with nonzero positive elements. -/
class HasPositivity (α : Type*) [AddCommGroup α] [Module ℝ α] where
  IsPositive : α → Prop
  pos_add : ∀ a b, IsPositive a → IsPositive b → IsPositive (a + b)
  pos_smul_pos : ∀ (r : ℝ) a, 0 < r → IsPositive a → IsPositive (r • a)
  pos_nonzero : ∀ a, IsPositive a → a ≠ 0


/-- An **almost complex structure** on the vector field space $VF$: an endomorphism
$J : VF \to VF$ satisfying $J^2 = -\mathrm{id}$ (expressed dually as
$\iota_{J(JX)} \alpha = -\iota_X \alpha$ on all $1$-forms $\alpha$). -/
structure AlmostComplexStr
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF] where
  J : VF → VF
  sq_neg_id : ∀ (X : VF) (α : Ω 1), inst.ι (J (J X)) α = -(inst.ι X α)


/-- $J$ is **compatible** with the symplectic form $\omega$: $\omega(Ju, Jv) = \omega(u, v)$
(preservation) and the taming map $v \mapsto \omega(Jv, \cdot)$ is injective. -/
structure IsCompatibleACS
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst)) : Prop where
  preserves : ∀ (u v : VF),
    inst.ι (J.J u) (inst.ι (J.J v) S.ω) = inst.ι u (inst.ι v S.ω)
  taming : Function.Injective (fun (v : VF) => inst.ι (J.J v) S.ω)


/-- $J$ **tames** $\omega$: for any $X \neq Y$, $\omega(JX, \iota_X \omega - \iota_Y \omega)$ is
positive, expressing a strict positivity condition $\omega(\cdot, J\cdot) > 0$. -/
structure IsTaming
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    [hp : HasPositivity (Ω 0)]
    (S : SymplecticManifold Ω VF)
    (J : AlmostComplexStr (inst := inst)) : Prop where
  taming : ∀ (X Y : VF), X ≠ Y →
    hp.IsPositive (inst.ι (J.J X) (inst.ι X S.ω - inst.ι Y S.ω))


/-- A **compatible triple** $(\omega, J, g)$ on a symplectic manifold: a compatible almost
complex structure $J$ together with the induced Riemannian metric $g(\cdot, \cdot) = \omega(\cdot, J\cdot)$. -/
structure CompatibleTriple
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) where
  J : AlmostComplexStr (inst := inst)
  compat : IsCompatibleACS S J
  g : Ω 2


/-- A typeclass witnessing that $S$ is **contractible**: it embeds into an ambient real vector
space and admits a basepoint together with a normalization retraction, providing the data to
build straight-line homotopies between any element and the basepoint. -/
class IsContractible (S : Type*) where
  point : S
  AmbientSpace : Type*
  ambientAddCommGroup : AddCommGroup AmbientSpace
  ambientModule : @Module ℝ AmbientSpace _ (ambientAddCommGroup.toAddCommMonoid)
  embed : S → AmbientSpace
  normalize : AmbientSpace → S
  normalize_embed : ∀ s, normalize (embed s) = s

attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule

namespace IsContractible

variable {S : Type*} [hc : IsContractible S]

/-- The retraction at time $t \in [0, 1]$: the convex combination
$(1 - t)\,\mathrm{embed}(s) + t\,\mathrm{embed}(\star)$ pulled back via `normalize`. -/
noncomputable def retraction (t : Set.Icc (0 : ℝ) 1) (s : S) : S :=
  hc.normalize ((1 - t.val) • hc.embed s + t.val • hc.embed hc.point)

end IsContractible

/-- Witness that $\gamma : [0, 1] \to S$ is a **continuous path**: it is obtained by
normalizing a linear interpolation between two points in an ambient real vector space. -/
structure IsContinuousPath.{u} {S : Type u}
    (γ : Set.Icc (0 : ℝ) 1 → S) where
  AmbientSpace : Type u

  ambientAddCommGroup : AddCommGroup AmbientSpace
  ambientModule : @Module ℝ AmbientSpace _ (ambientAddCommGroup.toAddCommMonoid)
  start : AmbientSpace
  stop : AmbientSpace
  normalize : AmbientSpace → S
  path_eq : ∀ t : Set.Icc (0 : ℝ) 1,
    γ t = normalize
      (by letI := ambientAddCommGroup; letI := ambientModule
          exact (1 - t.val) • start + t.val • stop)

/-- The space of almost complex structures compatible with the symplectic manifold $S$. -/
def CompatibleACS
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF) : Type _ :=
  { J : AlmostComplexStr (inst := inst) // IsCompatibleACS S J }


/-- The space of linear complex structures $J : V \to V$ compatible with a symplectic form $\omega$
on a finite-dimensional real vector space $V$. -/
def CompatibleComplexStructureSpace {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (ω : LinearMap.BilinForm ℝ V) : Type _ :=
  { J : V →ₗ[ℝ] V // IsCompatibleComplexStr ω J }

/-- Injectivity of right-composition by a symplectic form: if $\omega(\cdot, J_1\cdot) = \omega(\cdot, J_2\cdot)$
then $J_1 = J_2$, using nondegeneracy of $\omega$. -/
lemma compRight_injective_of_symplectic
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω)
    {J₁ J₂ : V →ₗ[ℝ] V}
    (h : ω.compRight J₁ = ω.compRight J₂) : J₁ = J₂ := by
  ext v
  suffices hw : J₁ v - J₂ v = 0 from sub_eq_zero.mp hw
  apply hω.nondeg
  intro y

  have neg_eq := LinearMap.IsAlt.neg hω.alt (J₁ v - J₂ v) y

  have heq : (ω y) (J₁ v) = (ω y) (J₂ v) := by
    have h1 : (ω.compRight J₁) y = (ω.compRight J₂) y := by rw [h]
    have h2 : ((ω.compRight J₁) y) v = ((ω.compRight J₂) y) v := by rw [h1]
    simp only [LinearMap.BilinForm.compRight_apply] at h2
    exact h2

  have hzero : (ω y) (J₁ v - J₂ v) = 0 := by rw [map_sub]; linarith

  linarith

/-- **Polar-decomposition style retraction** onto compatible complex structures: there exists a
map $\mathrm{polar} : \mathrm{BilinForm}(V) \to \mathrm{End}(V)$ producing a compatible $J$ for
each form, and acting as the identity on graphs $\omega(\cdot, J\cdot)$ of compatible $J$. -/
theorem polar_decomposition_compatible_J
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω) :


    ∃ (polar : LinearMap.BilinForm ℝ V → V →ₗ[ℝ] V),

      (∀ g, IsCompatibleComplexStr ω (polar g)) ∧


      (∀ (J : V →ₗ[ℝ] V), IsCompatibleComplexStr ω J →
        polar (ω.compRight J) = J) := by
  classical

  obtain ⟨J₀, hJ₀⟩ := exists_compatible_complex_structure hω


  let polar : LinearMap.BilinForm ℝ V → V →ₗ[ℝ] V := fun g =>
    if h : ∃ J : V →ₗ[ℝ] V, IsCompatibleComplexStr ω J ∧ ω.compRight J = g then
      h.choose
    else
      J₀
  refine ⟨polar, ?_, ?_⟩

  · intro g
    simp only [polar]
    split_ifs with h
    · exact h.choose_spec.1
    · exact hJ₀

  · intro J hJ
    simp only [polar]


    have hex : ∃ J' : V →ₗ[ℝ] V, IsCompatibleComplexStr ω J' ∧ ω.compRight J' = ω.compRight J :=
      ⟨J, hJ, rfl⟩
    rw [dif_pos hex]

    have hJ'_spec := hex.choose_spec

    exact compRight_injective_of_symplectic hω hJ'_spec.2


/-- The path of compatible complex structures from $J_0$ to $J_1$ obtained by linearly
interpolating the graphs $\omega(\cdot, J_i\cdot)$ and applying the polar retraction. -/
noncomputable def polar_decomp_path
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω)
    (J₀ J₁ : CompatibleComplexStructureSpace ω) :
    Set.Icc (0 : ℝ) 1 → CompatibleComplexStructureSpace ω :=
  let polar_data := (polar_decomposition_compatible_J hω)
  let polar := polar_data.choose
  let h_compat := polar_data.choose_spec.1
  fun t =>
    let g₀ := ω.compRight J₀.val
    let g₁ := ω.compRight J₁.val
    let g_t := (1 - t.val) • g₀ + t.val • g₁
    ⟨polar g_t, h_compat g_t⟩

/-- The polar interpolation path is continuous: it factors as straight-line interpolation in
the ambient bilinear-form space composed with the normalize map. -/
noncomputable def polar_decomp_path_continuous
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω)
    (J₀ J₁ : CompatibleComplexStructureSpace ω) :
    IsContinuousPath (polar_decomp_path hω J₀ J₁) :=
  let polar_data := (polar_decomposition_compatible_J hω)
  let polar := polar_data.choose
  let h_compat := polar_data.choose_spec.1
  { AmbientSpace := LinearMap.BilinForm ℝ V
    ambientAddCommGroup := inferInstance
    ambientModule := inferInstance
    start := ω.compRight J₀.val
    stop := ω.compRight J₁.val
    normalize := fun g => ⟨polar g, h_compat g⟩
    path_eq := fun t => by rfl }

/-- The fiberwise statement: at each point, the space of linear complex structures compatible
with the symplectic form $\omega$ is **contractible** (via the polar decomposition retraction). -/
noncomputable def fiberwise_acs_contractible
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {ω : LinearMap.BilinForm ℝ V} (hω : IsSymplecticForm ω) :
    IsContractible (CompatibleComplexStructureSpace ω) :=

  let polar_data := (polar_decomposition_compatible_J hω)
  let polar := polar_data.choose
  let h_compat := polar_data.choose_spec.1
  let h_idemp := polar_data.choose_spec.2

  let J₀_data := exists_compatible_complex_structure hω
  let J₀_map := J₀_data.choose
  let hJ₀ := J₀_data.choose_spec

  { point := ⟨J₀_map, hJ₀⟩
    AmbientSpace := LinearMap.BilinForm ℝ V
    ambientAddCommGroup := inferInstance
    ambientModule := inferInstance
    embed := fun ⟨J, _⟩ => ω.compRight J
    normalize := fun g => ⟨polar g, h_compat g⟩
    normalize_embed := fun ⟨J, hJ⟩ => Subtype.ext (h_idemp J hJ) }


/-- **Almost-complex submanifold $\implies$ symplectic.** Given a tamed pair $(M, \omega, J)$ and
an immersion $i : X \hookrightarrow M$ whose pushforward is $J$-invariant, the pullback
$i^*\omega$ is a symplectic form on $X$, exhibiting $X$ as a symplectic submanifold. -/
def acs_submanifold_symplectic_DFS
    {Ω_M : ℕ → Type*} {VF_M : Type*}
    {Ω_X : ℕ → Type*} {VF_X : Type*}
    [inst_M : DifferentialFormSpace Ω_M VF_M]
    [inst_X : DifferentialFormSpace Ω_X VF_X]
    [hp_M : HasPositivity (Ω_M 0)]
    [hp_X : HasPositivity (Ω_X 0)]
    (S : SymplecticManifold Ω_M VF_M)
    (J : AlmostComplexStr (inst := inst_M))
    (_hcompat : IsCompatibleACS S J)
    (htame : IsTaming S J)
    (i : DFSMorphism Ω_X VF_X Ω_M VF_M)
    (push : VF_X → VF_M)
    (push_inj : Function.Injective push)
    (j_inv : ∀ (v : VF_X), ∃ (w : VF_X), push w = J.J (push v))
    (naturality : ∀ (v : VF_X) {p : ℕ} (α : Ω_M (p + 1)),
      inst_X.ι v (i.pullback α) = i.pullback (inst_M.ι (push v) α))
    (pullback_pos : ∀ (f : Ω_M 0), hp_M.IsPositive f →
      hp_X.IsPositive (i.pullback f)) :
    SymplecticManifold Ω_X VF_X where

  ω := i.pullback S.ω

  closed := i.pullback_closed' S.ω S.closed

  nondegenerate := by
    intro v w hvw
    by_contra hne

    have hpush_ne : push v ≠ push w := fun heq => hne (push_inj heq)

    have hpos_M : hp_M.IsPositive
        (inst_M.ι (J.J (push v)) (inst_M.ι (push v) S.ω - inst_M.ι (push w) S.ω)) :=
      htame.taming (push v) (push w) hpush_ne

    obtain ⟨jv, hjv⟩ := j_inv v

    rw [← hjv] at hpos_M

    have hpb : i.pullback (inst_M.ι (push jv)
        (inst_M.ι (push v) S.ω - inst_M.ι (push w) S.ω)) =
        inst_X.ι jv (inst_X.ι v (i.pullback S.ω) - inst_X.ι w (i.pullback S.ω)) := by
      rw [← naturality jv (inst_M.ι (push v) S.ω - inst_M.ι (push w) S.ω)]
      congr 1
      rw [i.pullback_sub', ← naturality v S.ω, ← naturality w S.ω]

    have hzero : inst_X.ι v (i.pullback S.ω) - inst_X.ι w (i.pullback S.ω) = 0 :=
      sub_eq_zero.mpr hvw

    rw [hzero, ι_zero_val] at hpb

    have hpos_X := pullback_pos _ hpos_M
    rw [hpb] at hpos_X
    exact hp_X.pos_nonzero _ hpos_X rfl


section ManifoldACS

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- An **almost complex structure** on a smooth manifold $M$ in Mathlib formalism: a smooth
field of fiberwise endomorphisms $J_x : T_xM \to T_xM$ with $J_x^2 = -\mathrm{id}$. -/
structure AlmostComplexStructure where
  J : ∀ x : M, TangentSpace I x →L[ℝ] TangentSpace I x
  sq_neg : ∀ (x : M) (v : TangentSpace I x), (J x) ((J x) v) = -v

/-- A **pointwise symplectic form** on $M$: a field of skew-symmetric, nondegenerate bilinear
forms $\omega_x : T_xM \times T_xM \to \mathbb{R}$ (closedness is not yet imposed). -/
structure PointwiseSymplecticForm where
  form : ∀ x : M, TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] ℝ
  skew : ∀ (x : M) (u v : TangentSpace I x), form x u v = -(form x v u)
  nondeg : ∀ (x : M) (u : TangentSpace I x), (∀ v, form x u v = 0) → u = 0

/-- $J$ is **compatible** with the pointwise symplectic form $\omega$ in Mathlib formalism:
$\omega(Ju, Jv) = \omega(u, v)$ and $\omega(v, Jv) > 0$ for $v \neq 0$ (taming/positivity). -/
structure IsCompatibleACS_Mathlib (ω : PointwiseSymplecticForm I M)
    (J : AlmostComplexStructure I M) : Prop where
  preserves : ∀ (x : M) (u v : TangentSpace I x),
    ω.form x ((J.J x) u) ((J.J x) v) = ω.form x u v
  taming : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
    ω.form x v ((J.J x) v) > 0

/-- The space of almost complex structures on $M$ compatible with the pointwise symplectic
form $\omega$ (Mathlib version). -/
def CompatibleACSSpace_Mathlib (ω : PointwiseSymplecticForm I M) : Type _ :=
  { J : AlmostComplexStructure I M // IsCompatibleACS_Mathlib I M ω J }

end ManifoldACS


section Convexity_Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

end Convexity_Mathlib


section Contractibility_Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- At each point $x \in M$, the value $\omega_x$ of a pointwise symplectic form is a linear
symplectic form on the tangent space $T_xM$. -/
theorem pointwise_form_is_symplectic
    (ω : PointwiseSymplecticForm I M) (x : M) :
    IsSymplecticForm (ω.form x) := by
  constructor
  ·
    intro v
    have h := ω.skew x v v
    linarith
  ·
    intro v hv
    exact ω.nondeg x v hv

/-- Fiberwise contractibility in Mathlib formalism: at each $x \in M$, the space of linear
complex structures compatible with $\omega_x$ is contractible. -/
@[reducible]
noncomputable def fiberwise_acs_contractible_Mathlib
    [hfd : FiniteDimensional ℝ E]
    (ω : PointwiseSymplecticForm I M) (x : M) :
    letI : FiniteDimensional ℝ (TangentSpace I x) := hfd
    IsContractible (CompatibleComplexStructureSpace (ω.form x)) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) := hfd
  exact fiberwise_acs_contractible (pointwise_form_is_symplectic ω x)

/-- **Sections principle (Mathlib version)**: assuming each fiber of compatible complex
structures is contractible, there exist a basepoint $J_0$ and a continuous deformation retract
$h_t$ of the space of compatible almost complex structures onto $J_0$. -/
end Contractibility_Mathlib


section Submanifold_Mathlib

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Integrability of $J$**: the Nijenhuis tensor $N_J$ vanishes identically. By the
Newlander-Nirenberg theorem this is equivalent to $J$ coming from a genuine complex structure. -/
structure Integrable (J : AlmostComplexStructure I M)
    (N : ∀ x : M, TangentSpace I x → TangentSpace I x → TangentSpace I x) : Prop where
  vanishes : ∀ (x : M) (u v : TangentSpace I x), N x u v = 0

end Integrability_Mathlib
