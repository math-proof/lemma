/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/AlmostComplexManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Class.v1.Atlas.GeometryOfManifolds.code.TangentBundleDFS
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.MFDeriv.Defs
import Theorem.v1.Atlas.GeometryOfManifolds.code.AlmostComplexManifolds
set_option autoImplicit false

open DifferentialFormSpace SymplecticLinearAlgebra


attribute [reducible, instance] IsContractible.ambientAddCommGroup IsContractible.ambientModule


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


