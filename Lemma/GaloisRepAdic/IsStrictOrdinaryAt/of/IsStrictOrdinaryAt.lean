import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.GaloisRep.StrictOrdinary
import Lemma.Int.P2MUtil


/--
[GaloisRepAdic_isStrictOrdinaryAt_of_isEquiv](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_isStrictOrdinaryAt_of_isEquiv.lean)
-/

private lemma  map_apply_symm
    {A : Type}
    [CommRing A]
    [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A}
    (e : GaloisRepAdic.Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : ρ₂.V) :
    ρ₂.ρ σ y = e.toLinearEquiv (ρ₁.ρ σ (e.toLinearEquiv.symm y)) := by
  rw [e.map_apply, LinearEquiv.apply_symm_apply]

private lemma  map_span_singleton
    {A : Type}
    [CommRing A]
    [IsLocalRing A]
    {ρ₁ ρ₂ : GaloisRepAdic A}
    (e : GaloisRepAdic.Equiv ρ₁ ρ₂) (w : ρ₁.V) :
    (A ∙ w).map (e.toLinearEquiv : ρ₁.V →ₗ[A] ρ₂.V) = A ∙ e.toLinearEquiv w := by
  rw [Submodule.map_span, Set.image_singleton]
  rfl


@[path]
private lemma main
  [CommRing A] [IsLocalRing A]
  {ρ₁ ρ₂ : GaloisRepAdic A}
  {e : ρ₁.IsEquiv ρ₂}
  {p : ℕ}
-- given
  (h : ρ₁.IsStrictOrdinaryAt p) :
-- imply
  ρ₂.IsStrictOrdinaryAt p := by
-- proof
  obtain ⟨e⟩ := e
  obtain ⟨hpA, h⟩ := h
  refine ⟨hpA, fun P hP => ?_⟩
  obtain ⟨L, ⟨b, rfl⟩, hD, hI, hS⟩ := h P hP
  set E : ρ₁.V ≃ₗ[A] ρ₂.V := e.toLinearEquiv with hE
  have hmem : ∀ {v : ρ₁.V}, v ∈ A ∙ b 0 → E v ∈ A ∙ E (b 0) := by
    intro v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  refine ⟨A ∙ E (b 0), ⟨b.map E, by rw [Module.Basis.map_apply]⟩, ?_, ?_, ?_⟩
  ·
    intro σ hσ v hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, map_apply_symm e, ← hE, LinearEquiv.symm_apply_apply]
    exact Submodule.smul_mem _ _ (hmem (hD σ hσ _ (Submodule.mem_span_singleton_self _)))
  ·
    intro σ hσ v
    have h1 : ρ₂.ρ σ v - v = E (ρ₁.ρ σ (E.symm v) - E.symm v) := by
      rw [map_sub, LinearEquiv.apply_symm_apply, map_apply_symm e, ← hE]
    rw [h1]
    exact hmem (hI σ hσ _)
  ·
    intro σ hσ
    obtain ⟨x, z, hx, hz, hc⟩ := hS σ hσ
    refine ⟨x, z, ?_, ?_, hc⟩
    · intro w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      rw [map_apply_symm e, ← hE, map_smul, LinearEquiv.symm_apply_apply,
        ← map_smul E, hx _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)),
        map_smul, map_smul, smul_comm]
    · intro v
      have h1 : ρ₂.ρ σ v - z • v = E (ρ₁.ρ σ (E.symm v) - z • E.symm v) := by
        rw [map_sub, map_smul, LinearEquiv.apply_symm_apply, map_apply_symm e, ← hE]
      rw [h1]
      exact hmem (hz _)


-- created on 2026-10-23
