import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GaloisRep_StrictOrdinary
import Lemma.Int.P2MUtil

open GaloisRepAdic

/--
[GaloisRepAdic_strictOrdinaryCondition_of_isEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_strictOrdinaryCondition_of_isEquiv.lean)
-/

private lemma  conj_eq
    {A : Type}
    [CommRing A]
    [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ₂.ρ σ = (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V) ∘ₗ ρ₁.ρ σ ∘ₗ
      (e.toLinearEquiv.symm : ρ₂.V →ₗ[A] ρ₁.V) := by
  refine LinearMap.ext fun y => ?_
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    e.map_apply, LinearEquiv.apply_symm_apply]

private lemma  det_apply_eq
    {A : Type}
    [CommRing A]
    [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det (ρ₂.ρ σ) = LinearMap.det (ρ₁.ρ σ) := by
  rw [conj_eq e σ, LinearMap.det_conj]

private lemma  detIsCyclotomic_of_isEquiv
    {A : Type}
    [CommRing A]
    [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.DetIsCyclotomic p) : ρ₂.DetIsCyclotomic p := by
  obtain ⟨e⟩ := e
  refine ⟨h.1, fun n σ a hσ => ?_⟩
  rw [det_apply_eq e σ]
  exact h.2 n σ a hσ

private lemma  isUnramifiedAt_of_isEquiv
    {A : Type}
    [CommRing A]
    [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {q : ℕ}
    (h : ρ₁.IsUnramifiedAt q) : ρ₂.IsUnramifiedAt q := by
  obtain ⟨e⟩ := e
  intro P hP σ hσ
  refine LinearMap.ext fun w => ?_
  obtain ⟨v, rfl⟩ := e.toLinearEquiv.surjective w
  rw [← e.map_apply, h P hP σ hσ, Module.End.one_apply, Module.End.one_apply]

private lemma  isStrictOrdinaryAt_of_isEquiv
    {A : Type} [CommRing A] [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : ρ₁.IsEquiv ρ₂) {p : ℕ}
    (h : ρ₁.IsStrictOrdinaryAt p) : ρ₂.IsStrictOrdinaryAt p := by
  obtain ⟨f⟩ := e
  let E : ρ₁.V ≃ₗ[A] ρ₂.V := f.toLinearEquiv
  have hmap : ∀ σ v, E (ρ₁.ρ σ v) = ρ₂.ρ σ (E v) := fun σ v => f.map_apply σ v
  have hmap' : ∀ σ w, ρ₂.ρ σ w = E (ρ₁.ρ σ (E.symm w)) := fun σ w => by
    rw [hmap, LinearEquiv.apply_symm_apply]
  refine ⟨h.1, fun P hP => ?_⟩
  obtain ⟨L, ⟨b, hb⟩, hD, hI, hS⟩ := h.2 P hP
  refine ⟨L.map (E : ρ₁.V →ₗ[A] ρ₂.V), ⟨b.map E, ?_⟩, ?_, ?_, ?_⟩
  · rw [hb, Submodule.map_span, Set.image_singleton]; rfl
  · intro σ hσ w hw
    obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
    exact Submodule.mem_map.2 ⟨ρ₁.ρ σ v, hD σ hσ v hv, (hmap σ v)⟩
  · intro σ hσ w
    have := hI σ hσ (E.symm w)
    refine Submodule.mem_map.2 ⟨ρ₁.ρ σ (E.symm w) - E.symm w, this, ?_⟩
    simp only [LinearEquiv.coe_coe, map_sub]
    rw [hmap, LinearEquiv.apply_symm_apply]
  · intro σ hσ
    obtain ⟨x, z, hx, hz, hcong⟩ := hS σ hσ
    refine ⟨x, z, fun w hw => ?_, fun w => ?_, hcong⟩
    · obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.1 hw
      simp only [LinearEquiv.coe_coe]
      rw [← hmap, hx v hv, map_smul]
    · refine Submodule.mem_map.2 ⟨ρ₁.ρ σ (E.symm w) - z • E.symm w, hz (E.symm w), ?_⟩
      simp only [LinearEquiv.coe_coe, map_sub, map_smul]
      rw [hmap, LinearEquiv.apply_symm_apply]
@[path]
private lemma main
  [CommRing A] [IsLocalRing A] [CommRing 𝒪] [Algebra 𝒪 A]
  {ρ₁ ρ₂ : GaloisRepAdic A}
  {e : ρ₁.IsEquiv ρ₂}
  {p : ℕ}
  {S : Finset ℕ}
-- given
  (h : GaloisRep.strictOrdinaryCondition 𝒪 p S ρ₁) :
-- imply
  GaloisRep.strictOrdinaryCondition 𝒪 p S ρ₂ := by
-- proof
  obtain ⟨h₁, h₂, h₃⟩ := h
  exact ⟨detIsCyclotomic_of_isEquiv e h₁,
    isStrictOrdinaryAt_of_isEquiv e h₂,
    fun q hq hqS => isUnramifiedAt_of_isEquiv e (h₃ q hq hqS)⟩


-- created on 2026-10-23
