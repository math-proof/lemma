import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[Module_Invertible_exists_notMem_and_forall_exists_pow_smul_eq_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Invertible_exists_notMem_and_forall_exists_pow_smul_eq_smul.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M] [Module.Invertible R M]
  (p : Ideal R) [p.IsPrime] :
  -- imply
  ∃ t : R, t ∉ p ∧ ∃ m₀ : M, ∀ m : M, ∃ (n : ℕ) (r : R), t ^ n • m = r • m₀ := by
  -- proof
  classical
  have hfp : Module.FinitePresentation R M := Module.finitePresentation_of_projective R M
  let Rp := Localization.AtPrime p
  let Mp := LocalizedModule p.primeCompl M
  have hfree : Module.Free Rp Mp := inferInstance
  have hrk : Module.finrank Rp Mp = 1 := Module.Invertible.finrank_eq_one Rp Mp
  obtain ⟨t, ht, hfree', hrank⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) Rp
  refine ⟨t, ht, ?_⟩
  let S : Submonoid R := Submonoid.powers t
  let Rt := Localization S
  let Mt := LocalizedModule S M
  let f : M →ₗ[R] Mt := LocalizedModule.mkLinearMap S M
  let φ : RingHom Rt Rp := IsLocalization.map (M := S) (T := p.primeCompl) _
    (RingHom.id _) (Submonoid.powers_le.mpr ht)
  let _ : Nontrivial Rt := φ.domain_nontrivial
  let _ : Module.Free Rt Mt := hfree'
  let b : Module.Basis (Fin 1) Rt Mt := Module.basisUnique (Fin 1) (hrank.trans hrk)
  obtain ⟨⟨m₁, s₁⟩, hv⟩ := IsLocalizedModule.mk'_surjective S f (b 0)
  refine ⟨m₁, fun m => ?_⟩
  have hm : f m = b.repr (f m) 0 • b 0 := by
    conv_lhs => rw [← b.sum_repr (f m)]
    simp
  obtain ⟨⟨a, s₂⟩, hc⟩ := IsLocalization.mk'_surjective S (b.repr (f m) 0)
  change IsLocalizedModule.mk' f m₁ s₁ = b 0 at hv
  rw [← hc, ← hv, IsLocalizedModule.mk'_smul_mk' Rt, ← IsLocalizedModule.mk'_one S f,
    IsLocalizedModule.mk'_eq_mk'_iff] at hm
  obtain ⟨c, hc'⟩ := hm
  obtain ⟨_, ⟨i, rfl⟩⟩ := c
  obtain ⟨_, ⟨j, rfl⟩⟩ := s₂
  obtain ⟨_, ⟨k, rfl⟩⟩ := s₁
  refine ⟨i + (j + k), t ^ i * a, ?_⟩
  simp only [Submonoid.smul_def, one_smul, mul_smul, pow_add] at hc' ⊢
  apply hc'.symm


-- created on 2026-10-20
