import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.DModulesII.Part6
open CategoryTheory DModulesII


namespace DModulesII

/--
[torsion_is_DSubmodule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModulesII.lean)
-/
@[path]
private lemma torsion_is_DSubmodule
  [CommRing R]
  [Ring D]
  {ι : R →+* D}
  {M : Type*}
  [AddCommGroup M]
  [Module D M]
  [IsLeibnizCompatible ι M]
  {f : R} :
-- imply
  ∃ (N : Submodule D M), ∀ v : M, v ∈ N ↔ ∃ n : ℕ, (ι f ^ n) • v = 0 := by
-- proof
  refine ⟨{
    carrier := {v | ∃ n : ℕ, (ι f ^ n) • v = 0}
    add_mem' := ?_
    zero_mem' := ?_
    smul_mem' := ?_
  }, fun v => Iff.rfl⟩
  ·
    intro a b ⟨na, ha⟩ ⟨nb, hb⟩
    refine ⟨na + nb, ?_⟩
    rw [smul_add]
    have ha' : ι f ^ (na + nb) • a = 0 := by
      have : ι f ^ (na + nb) = ι f ^ nb * ι f ^ na := by
        rw [pow_add]; exact (Commute.pow_pow (Commute.refl (ι f)) na nb).eq
      rw [this, mul_smul, ha, smul_zero]
    have hb' : ι f ^ (na + nb) • b = 0 := by
      rw [pow_add, mul_smul, hb, smul_zero]
    rw [ha', hb', add_zero]
  ·
    exact ⟨0, smul_zero _⟩
  ·
    intro d v ⟨n, hn⟩
    exact IsLeibnizCompatible.smul_torsion d f v n hn

end DModulesII

namespace DModulesII

/--
[sheafSupport_subset_implies_supported](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModulesII.lean)
-/
@[path]
private lemma sheafSupport_subset_implies_supported
  [CommRing R]
  [Ring D]
  {ι : R →+* D}
  {M : Type*}
  [AddCommGroup M]
  [Module D M]
  [IsSimpleModule D M]
  {I : Ideal R}
-- given
  (h : DModSheafSupport ι M ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
-- imply
  @IsSupportedOn R _ M _ (rModuleOf ι M) I := by
-- proof
  letI : Module R M := rModuleOf ι M
  intro f hf v
  suffices hsuff : PrimeSpectrum.zeroLocus ((Submodule.span R {v}).annihilator : Set R) ⊆
    PrimeSpectrum.zeroLocus (I : Set R) by
    rw [PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hsuff
    have hfrad := hsuff hf
    rw [Ideal.mem_radical_iff] at hfrad
    obtain ⟨N, hN⟩ := hfrad
    rw [Submodule.mem_annihilator_span_singleton] at hN
    exact ⟨N, hN⟩
  calc PrimeSpectrum.zeroLocus ((Submodule.span R {v}).annihilator : Set R)
    ⊆ DModSheafSupport ι M := by
      intro p hp
      simp only [DModSheafSupport, sheafSupport, Set.mem_iInter]
      intro J hJ
      simp only [PrimeSpectrum.mem_zeroLocus] at hp ⊢
      intro g hg
      obtain ⟨N, hN⟩ := hJ g hg v
      have hmem : g ^ N ∈ (Submodule.span R {v}).annihilator := by
        rwa [Submodule.mem_annihilator_span_singleton]
      exact p.2.mem_of_pow_mem N (hp hmem)
    _ ⊆ PrimeSpectrum.zeroLocus (I : Set R) := h

end DModulesII

namespace DModulesII

/--
[simple_DModule_support_preirreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModulesII.lean)
-/
@[path]
private lemma simple_DModule_support_preirreducible
  [CommRing R]
  [Ring D]
  {ι : R →+* D}
  {M : Type*}
  [AddCommGroup M]
  [Module D M]
  [IsSimpleModule D M]
  [IsLeibnizCompatible ι M]
  {z₁ z₂ : Set (PrimeSpectrum R)}
-- given
  (hz₁ : IsClosed z₁)
  (hz₂ : IsClosed z₂)
  (hsub : DModSheafSupport ι M ⊆ z₁ ∪ z₂) :
-- imply
  DModSheafSupport ι M ⊆ z₁ ∨ DModSheafSupport ι M ⊆ z₂ := by
-- proof
  set I₁ := PrimeSpectrum.vanishingIdeal z₁
  set I₂ := PrimeSpectrum.vanishingIdeal z₂
  have hz₁_eq : z₁ = PrimeSpectrum.zeroLocus (I₁ : Set R) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hz₁.closure_eq]
  have hz₂_eq : z₂ = PrimeSpectrum.zeroLocus (I₂ : Set R) := by
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hz₂.closure_eq]
  rw [hz₁_eq, hz₂_eq] at hsub ⊢
  rw [← PrimeSpectrum.zeroLocus_inf] at hsub
  have hsupp := sheafSupport_subset_implies_supported ι M (I₁ ⊓ I₂) hsub
  by_cases h₁ : @IsSupportedOn R _ M _ (rModuleOf ι M) I₁
  ·
    left; exact Set.iInter₂_subset I₁ h₁
  ·
    have h₁' : ∃ f₁ : R, f₁ ∈ I₁ ∧ ∃ v₀ : M, ∀ N : ℕ, ι (f₁ ^ N) • v₀ ≠ 0 := by
      by_contra h; push Not at h; exact h₁ (fun f hf v => h f hf v)
    obtain ⟨f₁, hf₁, v₀, hv₀⟩ := h₁'
    obtain ⟨T₁, hT₁⟩ := torsion_is_DSubmodule ι M f₁
    have hv₀_notin : v₀ ∉ T₁ := by
      rw [hT₁]; push Not; intro n
      have := hv₀ n; rwa [map_pow] at this
    have hT₁_bot : T₁ = ⊥ :=
      (IsSimpleOrder.eq_bot_or_eq_top T₁).resolve_right
        (fun h => hv₀_notin (h ▸ Submodule.mem_top))
    right; apply Set.iInter₂_subset I₂
    intro f₂ hf₂ v
    have hprod : f₁ * f₂ ∈ I₁ ⊓ I₂ :=
      ⟨Ideal.mul_mem_right f₂ I₁ hf₁, Ideal.mul_mem_left I₂ f₁ hf₂⟩
    obtain ⟨N, hN⟩ := hsupp (f₁ * f₂) hprod v
    have hcomm : Commute (ι f₁) (ι f₂) := by
      show ι f₁ * ι f₂ = ι f₂ * ι f₁
      rw [← map_mul, ← map_mul, mul_comm]
    have hmem : (ι f₂ ^ N) • v ∈ T₁ := by
      rw [hT₁]; exact ⟨N, by
        rw [← mul_smul, ← hcomm.mul_pow, ← map_mul, ← map_pow]
        exact hN⟩
    rw [hT₁_bot, Submodule.mem_bot] at hmem
    exact ⟨N, by show ι (f₂ ^ N) • v = 0; rw [map_pow]; exact hmem⟩

end DModulesII

namespace DModulesII

/--
[irreducible_DModule_support_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModulesII.lean)
-/
@[path]
private lemma irreducible_DModule_support_irreducible
  [CommRing R]
  [Ring D]
  {ι : R →+* D}
  {M : Type*}
  [AddCommGroup M]
  [Module D M]
  [IsSimpleModule D M]
  [IsLeibnizCompatible ι M] :
-- imply
  IsIrreducible (DModSheafSupport ι M) := by
-- proof
  have hnt : Nontrivial M := IsSimpleModule.nontrivial D M
  constructor
  ·
    obtain ⟨v, w, hvw⟩ := hnt.exists_pair_ne
    set x := v - w
    have hx : x ≠ 0 := sub_ne_zero.mpr hvw
    let annx : Ideal R := {
      carrier := {r : R | ι r • x = 0}
      add_mem' := fun {a b} (ha : ι a • x = 0) (hb : ι b • x = 0) => by
        show ι (a + b) • x = 0; rw [map_add, add_smul, ha, hb, add_zero]
      zero_mem' := by show ι 0 • x = 0; rw [map_zero, zero_smul]
      smul_mem' := fun c {r} (hr : ι r • x = 0) => by
        show ι (c * r) • x = 0; rw [map_mul, mul_smul, hr, smul_zero]
    }
    have hannx_proper : annx ≠ ⊤ := by
      rw [Ideal.ne_top_iff_one]
      show ¬ (ι 1 • x = 0)
      rw [map_one, one_smul]; exact hx
    obtain ⟨m, hm_max, hm_le⟩ := Ideal.exists_le_maximal annx hannx_proper
    refine ⟨⟨m, hm_max.isPrime⟩, ?_⟩
    simp only [DModSheafSupport, sheafSupport, Set.mem_iInter]
    intro I hI
    rw [PrimeSpectrum.mem_zeroLocus]
    intro f hfI
    obtain ⟨N, hN⟩ := hI f hfI x
    have hfN_annx : f ^ N ∈ annx := by show ι (f ^ N) • x = 0; exact hN
    exact hm_max.isPrime.mem_of_pow_mem N (hm_le hfN_annx)
  ·
    rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro z₁ z₂ hz₁ hz₂ hsub
    exact simple_DModule_support_preirreducible ι M z₁ z₂ hz₁ hz₂ hsub

end DModulesII

namespace DModulesII

/--
[isKEquivDModBB_eq_strongKEquivDModPred](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModulesII.lean)
-/
@[path]
private lemma isKEquivDModBB_eq_strongKEquivDModPred
  {k : Type u_aag}
  [Field k]
  {k' : Type u_aag}
  [Field k']
  {bd : BBLocalizationData k'} :
-- imply
  IsKEquivDModBB bd = StrongKEquivDModPred k' bd.K bd.𝔨 bd.D (bd.lieToD.comp bd.ι𝔨) := by
-- proof
  ext M
  simp only [IsKEquivDModBB, StrongKEquivDModPred]
  constructor
  · rintro ⟨ga, hDlin, la, hlie, hact⟩; exact ⟨ga, hDlin, la, hlie, hact⟩
  · rintro ⟨ga, hDlin, la, hlie, hact⟩; exact ⟨ga, hDlin, la, hlie, hact⟩

end DModulesII

namespace DModulesII

/--
[isGKModBB_eq_compatibleKActionPred](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModulesII.lean)
-/
@[path]
private lemma isGKModBB_eq_compatibleKActionPred
  {k : Type u_aag}
  [Field k]
  {k' : Type u_aag}
  [Field k']
  {bd : BBLocalizationData k'} :
-- imply
  IsGKModBB bd = CompatibleKActionPred k' bd.K bd.𝔨 bd.D (bd.lieToD.comp bd.ι𝔨) bd.Ad_K := by
-- proof
  ext M
  simp only [IsGKModBB, CompatibleKActionPred]
  constructor
  · rintro ⟨ga, hfin, la, hcoinc, hcompat⟩; exact ⟨ga, hfin, la, hcoinc, hcompat⟩
  · rintro ⟨ga, hfin, la, hcoinc, hcompat⟩; exact ⟨ga, hfin, la, hcoinc, hcompat⟩

end DModulesII


-- created on 2026-10-23
-- updated on 2026-10-24
