import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[LinearMap_finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {A₁ A₂ A₃ : Type v} [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₂] [Module k A₂] [AddCommGroup A₃] [Module k A₃]
  {B₁ B₂ B₃ : Type v} [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₂] [Module k B₂] [AddCommGroup B₃] [Module k B₃]
  (d₁ : A₁ →ₗ[k] B₁) (d₂ : A₂ →ₗ[k] B₂) (d₃ : A₃ →ₗ[k] B₃) [FiniteDimensional k (LinearMap.ker d₂)] [FiniteDimensional k (B₂ ⧸ LinearMap.range d₂)] [FiniteDimensional k (LinearMap.ker d₃)]
  (f₁ : A₁ →ₗ[k] A₂) (f₂ : A₂ →ₗ[k] A₃) (g₁ : B₁ →ₗ[k] B₂) (g₂ : B₂ →ₗ[k] B₃)
  (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
  (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (_ : Function.Surjective g₂)
  (h₁ : LinearMap.comp g₁ d₁ = LinearMap.comp d₂ f₁) (h₂ : LinearMap.comp g₂ d₂ = LinearMap.comp d₃ f₂) :
  -- imply
  FiniteDimensional k (LinearMap.ker d₁) ∧ FiniteDimensional k (B₁ ⧸ LinearMap.range d₁) := by
  -- proof
  classical
  have hc₁ : ∀ a, g₁ (d₁ a) = d₂ (f₁ a) := fun a => congrArg (fun φ : A₁ →ₗ[k] B₂ => φ a) h₁
  have hc₂ : ∀ a, g₂ (d₂ a) = d₃ (f₂ a) := fun a => congrArg (fun φ : A₂ →ₗ[k] B₃ => φ a) h₂
  refine ⟨?_, ?_⟩
  ·
    have hmem : ∀ a : LinearMap.ker d₁, (LinearMap.comp f₁ (LinearMap.ker d₁).subtype) a ∈ LinearMap.ker d₂ := by
      intro a
      rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.subtype_apply, ← hc₁, LinearMap.mem_ker.mp a.2, map_zero]
    let ι : LinearMap.ker d₁ →ₗ[k] LinearMap.ker d₂ := LinearMap.codRestrict (LinearMap.ker d₂) (LinearMap.comp f₁ (LinearMap.ker d₁).subtype) hmem
    refine Module.Finite.of_injective ι ?_
    intro a b h
    apply Subtype.ext
    apply hf₁
    apply congrArg Subtype.val h
  ·
    have hle : LinearMap.range d₁ ≤ (LinearMap.range d₂).comap g₁ := by
      rintro _ ⟨a, rfl⟩
      exact ⟨f₁ a, (hc₁ a).symm⟩
    let φ : (B₁ ⧸ LinearMap.range d₁) →ₗ[k] (B₂ ⧸ LinearMap.range d₂) := Submodule.mapQ _ _ g₁ hle
    obtain ⟨σ, hσ⟩ := LinearMap.exists_rightInverse_of_surjective f₂ (LinearMap.range_eq_top.mpr hf₂)
    have hσ' : ∀ c, f₂ (σ c) = c := fun c => congrArg (fun ψ : A₃ →ₗ[k] A₃ => ψ c) hσ
    let e := LinearEquiv.ofInjective g₁ hg₁
    have hker : ∀ a : A₂, d₃ (f₂ a) = 0 → d₂ a ∈ LinearMap.range g₁ := by
      intro a ha
      have : g₂ (d₂ a) = 0 := by rw [hc₂, ha]
      obtain ⟨b, hb⟩ := (hg (d₂ a)).mp this
      exact ⟨b, hb⟩
    have hpremem : ∀ c : LinearMap.ker d₃, (LinearMap.comp d₂ (LinearMap.comp σ (LinearMap.ker d₃).subtype)) c ∈ LinearMap.range g₁ := by
      intro c
      apply hker
      rw [LinearMap.comp_apply, Submodule.subtype_apply, hσ']
      apply LinearMap.mem_ker.mp c.2
    let pre : LinearMap.ker d₃ →ₗ[k] LinearMap.range g₁ := LinearMap.codRestrict (LinearMap.range g₁) (LinearMap.comp d₂ (LinearMap.comp σ (LinearMap.ker d₃).subtype)) hpremem
    let Λ : LinearMap.ker d₃ →ₗ[k] (B₁ ⧸ LinearMap.range d₁) := LinearMap.comp ((LinearMap.range d₁).mkQ) (LinearMap.comp e.symm.toLinearMap pre)
    have hkerφ : LinearMap.ker φ ≤ LinearMap.range Λ := by
      intro q hq
      obtain ⟨b₁, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      rw [LinearMap.mem_ker] at hq
      change Submodule.Quotient.mk (g₁ b₁) = (0 : B₂ ⧸ LinearMap.range d₂) at hq
      rw [Submodule.Quotient.mk_eq_zero] at hq
      obtain ⟨a₂, ha₂⟩ := hq
      have hc : d₃ (f₂ a₂) = 0 := by rw [← hc₂, ha₂, (hg (g₁ b₁)).mpr ⟨b₁, rfl⟩]
      refine ⟨⟨f₂ a₂, LinearMap.mem_ker.mpr hc⟩, ?_⟩
      obtain ⟨a₁, ha₁⟩ := (hf (σ (f₂ a₂) - a₂)).mp (by rw [map_sub, hσ', sub_self])
      have hd : d₂ (σ (f₂ a₂)) = g₁ (b₁ + d₁ a₁) := by
        rw [map_add, hc₁, ha₁, map_sub, ha₂]
        abel
      have hpre : (pre ⟨f₂ a₂, LinearMap.mem_ker.mpr hc⟩ : LinearMap.range g₁) = ⟨g₁ (b₁ + d₁ a₁), b₁ + d₁ a₁, rfl⟩ := by
        apply Subtype.ext
        change d₂ (σ (f₂ a₂)) = g₁ (b₁ + d₁ a₁)
        apply hd
      have he : e.symm ⟨g₁ (b₁ + d₁ a₁), b₁ + d₁ a₁, rfl⟩ = b₁ + d₁ a₁ := by
        apply e.injective
        rw [LinearEquiv.apply_symm_apply]
        apply Subtype.ext
        rw [LinearEquiv.ofInjective_apply]
      change (LinearMap.range d₁).mkQ (e.symm (pre ⟨f₂ a₂, _⟩)) = Submodule.Quotient.mk b₁
      rw [hpre, he, Submodule.mkQ_apply, Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self d₁ a₁), add_zero]
    let _ : Module.Finite k (LinearMap.range Λ) := inferInstance
    have hkfg : (LinearMap.ker φ).FG := (Module.Finite.iff_fg.mp (Module.Finite.of_injective (Submodule.inclusion hkerφ) (Submodule.inclusion_injective hkerφ)))
    have hrfg : ((⊤ : Submodule k (B₁ ⧸ LinearMap.range d₁)).map φ).FG := IsNoetherian.noetherian _
    refine ⟨?_⟩
    refine Submodule.fg_of_fg_map_of_fg_inf_ker φ hrfg ?_
    rw [top_inf_eq]
    apply hkfg


-- created on 2026-10-20
