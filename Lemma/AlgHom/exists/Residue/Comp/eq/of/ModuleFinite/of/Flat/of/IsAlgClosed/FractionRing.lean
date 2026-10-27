import Mathlib
import Initialize.Tactic.Attr.Basic
open Polynomial


/--
[AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgHom_exists_residue_comp_eq_of_moduleFinite_of_flat_of_isAlgClosed_fractionRing.lean)
-/

private lemma exists_apply_eq_of_monic_of_eval₂_eq_zero (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [IsAlgClosed K] {D : Type*} [CommRing D] [IsDomain D] (i : A →+* D) : ∀ (n : ℕ) (f : A[X]), f.Monic → f.natDegree = n → ∀ c : D, f.eval₂ i c = 0 →
      ∃ b : A, i b = c := by
  have hinjBL : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  intro n
  induction n with
  | zero =>
      intro f hf hn c hc
      have h1 : f = 1 := hf.natDegree_eq_zero.mp hn
      rw [h1, eval₂_one] at hc
      exact absurd hc one_ne_zero
  | succ n ih =>
      intro f hf hn c hc
      have hdeg : (f.map (algebraMap A K)).degree ≠ 0 := by
        rw [hf.degree_map, degree_eq_natDegree hf.ne_zero, hn]
        exact_mod_cast Nat.succ_ne_zero n
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_root _ hdeg
      have hint : IsIntegral A r := ⟨f, hf, by rwa [IsRoot.def, eval_map] at hr⟩
      obtain ⟨b, hb⟩ := (IsIntegrallyClosed.isIntegral_iff (K := K)).mp hint
      have hfb : f.IsRoot b := by
        rw [IsRoot.def]
        apply hinjBL
        rwa [map_zero, ← eval₂_at_apply, hb, ← eval_map]
      have hfac : (X - C b) * (f.divByMonic (X - C b)) = f := mul_divByMonic_eq_iff_isRoot.mpr hfb
      set g := f.divByMonic (X - C b) with hg
      have hgm : g.Monic := (monic_X_sub_C b).of_mul_monic_left (by rwa [hfac])
      have hgn : g.natDegree = n := by
        have h := (monic_X_sub_C b).natDegree_mul hgm
        rw [hfac, hn, natDegree_X_sub_C] at h
        omega
      have hc' : (X - C b).eval₂ i c * g.eval₂ i c = 0 := by rw [← eval₂_mul, hfac, hc]
      obtain h0 | h0 := mul_eq_zero.mp hc'
      ·
        refine ⟨b, ?_⟩
        rwa [eval₂_sub, eval₂_X, eval₂_C, sub_eq_zero, eq_comm] at h0
      ·
        exact ih g hgm hgn c h0

private lemma surjective_of_isIntegral (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [IsAlgClosed K] {D : Type*} [CommRing D] [IsDomain D] (i : A →+* D) (hi : i.IsIntegral) : Function.Surjective i := fun c => by
  obtain ⟨f, hf, hfc⟩ := hi c
  exact exists_apply_eq_of_monic_of_eval₂_eq_zero A K i f.natDegree f hf rfl c hfc

private lemma mk_comp_injective_of_mem_minimalPrimes {A : Type*} [CommRing A] {S' : Type*} [CommRing S'] (i : A →+* S') (hnzd : ∀ b : A, b ≠ 0 → i b ∈ nonZeroDivisors S') {𝔮 : Ideal S'} (h𝔮 : 𝔮 ∈ minimalPrimes S') : Function.Injective ((Ideal.Quotient.mk 𝔮).comp i) := by
  intro b₁ b₂ h
  by_contra hne
  change Ideal.Quotient.mk 𝔮 (i b₁) = Ideal.Quotient.mk 𝔮 (i b₂) at h
  have hmem : i b₁ - i b₂ ∈ 𝔮 := Ideal.Quotient.eq.mp h
  rw [← map_sub] at hmem
  exact Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔮) hmem
    (hnzd _ (sub_ne_zero.mpr hne))

private lemma mk_comp_bijective_of_mem_minimalPrimes (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [IsAlgClosed K] {S' : Type*} [CommRing S'] (i : A →+* S') (hint : i.IsIntegral) (hnzd : ∀ b : A, b ≠ 0 → i b ∈ nonZeroDivisors S') {𝔮 : Ideal S'} (h𝔮 : 𝔮 ∈ minimalPrimes S') : Function.Bijective ((Ideal.Quotient.mk 𝔮).comp i) := by
  have : 𝔮.IsPrime := h𝔮.1.1
  exact ⟨mk_comp_injective_of_mem_minimalPrimes i hnzd h𝔮,
    surjective_of_isIntegral A K ((Ideal.Quotient.mk 𝔮).comp i)
      (RingHom.IsIntegral.trans _ _ hint
        (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective))⟩

private lemma exists_ringHom_forall_sub_mem (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [IsAlgClosed K] {S' : Type*} [CommRing S'] (i : A →+* S') (hint : i.IsIntegral) (hnzd : ∀ b : A, b ≠ 0 → i b ∈ nonZeroDivisors S') (𝔪₀ : Ideal S') [𝔪₀.IsPrime] : ∃ lam : S' →+* A, (∀ b : A, lam (i b) = b) ∧ ∀ s : S', s - i (lam s) ∈ 𝔪₀ := by
  obtain ⟨𝔮, h𝔮, hle⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal S') ≤ 𝔪₀)
  have : 𝔮.IsPrime := h𝔮.1.1
  set e := RingEquiv.ofBijective _ (mk_comp_bijective_of_mem_minimalPrimes A K i hint hnzd h𝔮)
    with he
  refine ⟨e.symm.toRingHom.comp (Ideal.Quotient.mk 𝔮), fun b => ?_, fun s => hle ?_⟩
  ·
    show e.symm (e b) = b
    exact e.symm_apply_apply b
  ·
    apply Ideal.Quotient.eq.mp
    show Ideal.Quotient.mk 𝔮 s = e (e.symm (Ideal.Quotient.mk 𝔮 s))
    exact (e.apply_symm_apply _).symm
@[path]
private lemma main
  [CommRing A] [IsDomain A] [IsLocalRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [IsAlgClosed K] [CommRing H] [Algebra A H] [Module.Finite A H] [Module.Flat A H]
  {ψ : H →ₐ[A] IsLocalRing.ResidueField A} :
-- imply
  ∃ φ : H →ₐ[A] A, ∀ h : H, IsLocalRing.residue A (φ h) = ψ h := by
-- proof
  have hint : (algebraMap A H).IsIntegral := fun x => Algebra.IsIntegral.isIntegral (R := A) x
  have hnzd : ∀ b : A, b ≠ 0 → algebraMap A H b ∈ nonZeroDivisors H := by
    intro b hb
    have hreg : IsSMulRegular H b :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hb)
    refine mem_nonZeroDivisors_iff_right.mpr fun x hx => ?_
    apply hreg
    show b • x = b • (0 : H)
    rwa [smul_zero, Algebra.smul_def, mul_comm]
  have : (RingHom.ker ψ.toRingHom).IsPrime := RingHom.ker_isPrime _
  obtain ⟨lam, h1, h2⟩ :=
    exists_ringHom_forall_sub_mem A K (algebraMap A H) hint hnzd (RingHom.ker ψ.toRingHom)
  refine ⟨{ lam with commutes' := h1 }, fun h => ?_⟩
  have hk : h - algebraMap A H (lam h) ∈ RingHom.ker ψ.toRingHom := h2 h
  rw [RingHom.mem_ker] at hk
  change ψ (h - algebraMap A H (lam h)) = 0 at hk
  rwa [map_sub, sub_eq_zero, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, eq_comm] at hk


-- created on 2026-10-10
