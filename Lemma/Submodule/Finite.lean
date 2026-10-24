import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private lemma isAddTorsionFree_submodule {V : Type u} [AddCommGroup V] [Module ℂ V] (Λ : Submodule ℤ V) : IsAddTorsionFree Λ := by
  refine ⟨fun n hn a b hab => ?_⟩
  apply Subtype.ext
  have h : (n : ℂ) • ((a : V) - b) = 0 := by
    have hab' : n • (a : V) = n • (b : V) := by
      have := congrArg (fun x : Λ => (x : V)) hab
      simpa using this
    rw [smul_sub, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, hab', sub_self]
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have := (smul_eq_zero.mp h).resolve_left hn'
  apply sub_eq_zero.mp this
private lemma moduleFinite_end {V : Type u} [AddCommGroup V] [Module ℂ V] (Λ : Submodule ℤ V) (hΛfg : Λ.FG) : Module.Finite ℤ (Λ →ₗ[ℤ] Λ) := by
  let _ : Module.Finite ℤ Λ := Module.Finite.iff_fg.mpr hΛfg
  let _ : IsAddTorsionFree Λ := isAddTorsionFree_submodule Λ
  let _ : Module.IsTorsionFree ℤ Λ := inferInstance
  let _ : Module.Free ℤ Λ := inferInstance
  apply Module.Finite.linearMap ℤ ℤ Λ Λ
private noncomputable def opAlg {V : Type u} [AddCommGroup V] [Module ℂ V] {J : Type v} (S : J → V →ₗ[ℂ] V) : Subalgebra ℤ (V →ₗ[ℂ] V) := Algebra.adjoin ℤ (Set.range S)
private lemma opAlg_preserves {V : Type u} [AddCommGroup V] [Module ℂ V] (Λ : Submodule ℤ V) {J : Type v} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) : ∀ T ∈ opAlg S, ∀ x ∈ Λ, T x ∈ Λ := by
  intro T hT
  refine Algebra.adjoin_induction (p := fun T _ => ∀ x ∈ Λ, T x ∈ Λ) ?_ ?_ ?_ ?_ hT
  ·
    intro _ hj x hx
    obtain ⟨j, rfl⟩ := hj
    apply hS j x hx
  ·
    intro n x hx
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    apply Λ.smul_mem n hx
  ·
    intro T₁ T₂ _ _ h₁ h₂ x hx
    rw [LinearMap.add_apply]
    apply Λ.add_mem (h₁ x hx) (h₂ x hx)
  ·
    intro T₁ T₂ _ _ h₁ h₂ x hx
    rw [Module.End.mul_apply]
    apply h₁ _ (h₂ x hx)
private noncomputable def res {V : Type u} [AddCommGroup V] [Module ℂ V] (Λ : Submodule ℤ V) {J : Type v} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) : opAlg S →ₗ[ℤ] (Λ →ₗ[ℤ] Λ) where
  toFun T := (T.1.restrictScalars ℤ).restrict (fun x hx => opAlg_preserves Λ S hS T.1 T.2 x hx)
  map_add' _ _ := by
    ext x
    rfl
  map_smul' _ _ := by
    ext x
    simp [LinearMap.restrict_apply]
private lemma res_apply {V : Type u} [AddCommGroup V] [Module ℂ V] (Λ : Submodule ℤ V) {J : Type v} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) (T : opAlg S) (x : Λ) : ((res Λ S hS T x : Λ) : V) = T.1 x := rfl
private lemma res_injective {V : Type u} [AddCommGroup V] [Module ℂ V] (Λ : Submodule ℤ V) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤) {J : Type v} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) : Function.Injective (res Λ S hS) := by
  intro T₁ T₂ h
  apply Subtype.ext
  apply LinearMap.ext_on hΛspan
  intro x hx
  have := congrArg (fun F : Λ →ₗ[ℤ] Λ => ((F ⟨x, hx⟩ : Λ) : V)) h
  simpa [res_apply] using this
private lemma moduleFinite_opAlg {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (Λ : Submodule ℤ V) (hΛfg : Λ.FG) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤) {J : Type v} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) : Module.Finite ℤ (opAlg S) := by
  let _ := moduleFinite_end Λ hΛfg
  apply Module.Finite.of_injective (res Λ S hS) (res_injective Λ hΛspan S hS)
private noncomputable def eigAlg {V : Type u} [AddCommGroup V] [Module ℂ V] (v : V) : Subalgebra ℤ (V →ₗ[ℂ] V) where
  carrier := {T | ∃ μ : ℂ, T v = μ • v}
  mul_mem' := by
    intro T₁ T₂ h₁mem h₂mem
    obtain ⟨μ₁, h₁⟩ := h₁mem
    obtain ⟨μ₂, h₂⟩ := h₂mem
    refine ⟨μ₂ * μ₁, ?_⟩
    rw [Module.End.mul_apply, h₂, map_smul, h₁, smul_smul]
  add_mem' := by
    intro T₁ T₂ h₁mem h₂mem
    obtain ⟨μ₁, h₁⟩ := h₁mem
    obtain ⟨μ₂, h₂⟩ := h₂mem
    exact ⟨μ₁ + μ₂, by rw [LinearMap.add_apply, h₁, h₂, add_smul]⟩
  algebraMap_mem' n := ⟨n, by rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply, Int.cast_smul_eq_zsmul]⟩
private lemma mem_eigAlg {V : Type u} [AddCommGroup V] [Module ℂ V] {v : V} {T : V →ₗ[ℂ] V} : T ∈ eigAlg v ↔ ∃ μ : ℂ, T v = μ • v := Iff.rfl
private noncomputable def ev {V : Type u} [AddCommGroup V] [Module ℂ V] (v : V) (T : eigAlg v) : ℂ := (mem_eigAlg.mp T.2).choose
private lemma ev_spec {V : Type u} [AddCommGroup V] [Module ℂ V] (v : V) (T : eigAlg v) : T.1 v = ev v T • v := (mem_eigAlg.mp T.2).choose_spec
private lemma ev_unique {V : Type u} [AddCommGroup V] [Module ℂ V] {v : V} (hv0 : v ≠ 0) (T : eigAlg v) {μ : ℂ} (h : T.1 v = μ • v) : ev v T = μ := by
  have h1 := ev_spec v T
  rw [h] at h1
  apply (smul_left_injective ℂ hv0 h1).symm
private noncomputable def evHom {V : Type u} [AddCommGroup V] [Module ℂ V] {v : V} (hv0 : v ≠ 0) : eigAlg v →+* ℂ where
  toFun := ev v
  map_one' := ev_unique hv0 _ (by simp)
  map_mul' T₁ T₂ := by
    apply ev_unique hv0 _
    show T₁.1 (T₂.1 v) = _
    rw [ev_spec v T₂, map_smul, ev_spec v T₁, smul_smul, mul_comm]
  map_zero' := ev_unique hv0 _ (by simp)
  map_add' T₁ T₂ := by
    apply ev_unique hv0 _
    show T₁.1 v + T₂.1 v = _
    rw [ev_spec v T₁, ev_spec v T₂, add_smul]
private lemma helper_main {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (Λ : Submodule ℤ V) (hΛfg : Λ.FG) (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤) {J : Type v} (S : J → V →ₗ[ℂ] V) (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ) (lam : J → ℂ) (v : V) (hv0 : v ≠ 0) (hv : ∀ j : J, S j v = lam j • v) : Module.Finite ℤ (Algebra.adjoin ℤ (Set.range lam)) := by
  let _ := moduleFinite_opAlg Λ hΛfg hΛspan S hS
  have hle : opAlg S ≤ eigAlg v := by
    apply Algebra.adjoin_le
    intro T hT
    obtain ⟨j, rfl⟩ := hT
    exact ⟨lam j, hv j⟩
  let χ : opAlg S →+* ℂ := (evHom hv0).comp (Subalgebra.inclusion hle).toRingHom
  let χl : opAlg S →ₗ[ℤ] ℂ := χ.toIntAlgHom.toLinearMap
  let _ : Module.Finite ℤ (LinearMap.range χl) := Module.Finite.range χl
  have hsub : (Subalgebra.toSubmodule (Algebra.adjoin ℤ (Set.range lam))) ≤ LinearMap.range χl := by
    have hr : LinearMap.range χl = Subalgebra.toSubmodule χ.toIntAlgHom.range := by
      ext z
      simp only [LinearMap.mem_range, Subalgebra.mem_toSubmodule, AlgHom.mem_range]
      rfl
    rw [hr]
    apply Subalgebra.toSubmodule.monotone
    apply Algebra.adjoin_le
    intro μ hμ
    obtain ⟨j, rfl⟩ := hμ
    refine ⟨⟨S j, Algebra.subset_adjoin ⟨j, rfl⟩⟩, ?_⟩
    show ev v ⟨S j, _⟩ = lam j
    apply ev_unique hv0 _ (hv j)
  let _ : IsNoetherian ℤ (LinearMap.range χl) := isNoetherian_of_isNoetherianRing_of_finite ℤ _
  let f : Algebra.adjoin ℤ (Set.range lam) →ₗ[ℤ] LinearMap.range χl :=
    { toFun := fun x => ⟨x.1, hsub x.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg (fun z : LinearMap.range χl => (z : ℂ)) hxy
    apply this
  refine Module.Finite.of_injective f hf
/--
[Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_moduleFinite_adjoin_eigenvalues_of_map_le_of_span_eq_top.lean)
-/
@[path]
private lemma main
  {V : Type u} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {J : Type v}
  (Λ : Submodule ℤ V)
  (S : J → V →ₗ[ℂ] V)
  (lam : J → ℂ)
  (v : V)
  -- given
  (hΛfg : Λ.FG)
  (hΛspan : Submodule.span ℂ (Λ : Set V) = ⊤)
  (hS : ∀ (j : J), ∀ x ∈ Λ, S j x ∈ Λ)
  (hv0 : v ≠ 0)
  (hv : ∀ j : J, S j v = lam j • v) :
  -- imply
  Module.Finite ℤ (Algebra.adjoin ℤ (Set.range lam)) :=
  helper_main Λ hΛfg hΛspan S hS lam v hv0 hv


-- created on 2026-10-20
