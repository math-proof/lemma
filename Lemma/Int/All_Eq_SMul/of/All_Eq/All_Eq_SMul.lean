import Mathlib
import sympy.Basic


/--
[IharaLemma_resKer_localized](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IharaLemma_resKer_localized.lean)
-/
@[main]
private lemma main
  [CommRing R]
  {S : Submonoid R}
  {V Vk V' Vk' : Type*} [AddCommGroup V] [Module R V] [AddCommGroup Vk] [Module R Vk] [AddCommGroup V'] [Module R V'] [AddCommGroup Vk'] [Module R Vk']
  {ϖ : R}
  {redV : V →ₗ[R] Vk}
  {gV : V →ₗ[R] V'} [IsLocalizedModule S gV]
  {gK : Vk →ₗ[R] Vk'} [IsLocalizedModule S gK]
  {red' : V' →ₗ[R] Vk'}
-- given
  (hker : ∀ v, redV v = 0 → ∃ v₁, v = ϖ • v₁)
  (hsq : ∀ v, red' (gV v) = gK (redV v)) :
-- imply
  ∀ v' : V', red' v' = 0 → ∃ v₁' : V', v' = ϖ • v₁' := by
-- proof
  intro v' hv'
  obtain ⟨⟨v, s⟩, hs⟩ := IsLocalizedModule.surj S gV v'
  have hs' : (s : R) • v' = gV v := by rw [← Submonoid.smul_def]; exact hs
  have h0 : gK (redV v) = 0 := by
    rw [← hsq, ← hs', map_smul, hv', smul_zero]
  obtain ⟨t, ht⟩ := (IsLocalizedModule.eq_zero_iff S gK).mp h0
  rw [Submonoid.smul_def] at ht
  have ht' : redV ((t : R) • v) = 0 := by rw [map_smul, ht]
  obtain ⟨w, hw⟩ := hker _ ht'
  have key : ((t * s : S) : R) • v' = ϖ • gV w := by
    rw [Submonoid.coe_mul, mul_smul, hs', ← map_smul, hw, map_smul]
  obtain ⟨y, hy⟩ :=
    ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units gV (t * s))).2 (gV w)
  rw [Module.algebraMap_end_apply] at hy
  refine ⟨y, IsLocalizedModule.smul_injective gV (t * s) ?_⟩
  show (t * s) • v' = (t * s) • (ϖ • y)
  rw [Submonoid.smul_def, Submonoid.smul_def, key, smul_comm _ ϖ y, hy]


-- created on 2026-10-05
