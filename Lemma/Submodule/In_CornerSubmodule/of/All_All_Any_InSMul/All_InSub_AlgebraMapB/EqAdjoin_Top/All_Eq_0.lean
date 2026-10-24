import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_IharaLemma_IdempotentSplitting
open IsLocalRing IharaLemma


namespace Definitions
end Definitions


/--
[IharaLemma_mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IharaLemma_mem_cornerSubmodule_of_forall_exists_pow_sub_algebraMap_smul_mem.lean)
-/
@[path]
private lemma main
  [CommRing 𝒪] [IsLocalRing 𝒪] [CommRing B] [Algebra 𝒪 B] [AddCommGroup V] [Module 𝒪 V] [Module B V] [IsScalarTower 𝒪 B V]
  {S : IdempotentSplitting B}
  {i : Fin S.n}
  {G : Set B}
  {c : B → 𝒪}
  {v : V}
-- given
  (hsep : ∀ v : V, (∀ k : ℕ, v ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V)) → v = 0)
  (hG : Algebra.adjoin 𝒪 G = ⊤)
  (hc : ∀ g ∈ G, g - algebraMap 𝒪 B (c g) ∈ S.𝔪 i)
  (hv : ∀ g ∈ G, ∀ k : ℕ, ∃ n : ℕ, ((g - algebraMap 𝒪 B (c g)) ^ n) • v ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V)) :
-- imply
  v ∈ cornerSubmodule (M :=
  V) (S.e i) := by
-- proof
  classical
  set x : B → B := fun g => g - algebraMap 𝒪 B (c g) with hx
  have hsep_gen : ∀ j : Fin S.n, j ≠ i → ∃ g ∈ G, x g ∉ S.𝔪 j := by
    intro j hj
    by_contra hall
    push Not at hall
    have key : ∀ (𝔪 : Ideal B) [𝔪.IsMaximal], (∀ g ∈ G, x g ∈ 𝔪) →
        ∃ ψ : B →ₐ[𝒪] B ⧸ 𝔪, (∀ b, ψ b = Ideal.Quotient.mk 𝔪 b) ∧
          Function.Surjective (algebraMap 𝒪 (B ⧸ 𝔪)) := by
      intro 𝔪 _ h𝔪
      refine ⟨Ideal.Quotient.mkₐ 𝒪 𝔪, fun _ => rfl, ?_⟩
      have hbot : (⊤ : Subalgebra 𝒪 (B ⧸ 𝔪)) ≤ ⊥ := by
        have h1 : (⊤ : Subalgebra 𝒪 (B ⧸ 𝔪)) = (⊤ : Subalgebra 𝒪 B).map (Ideal.Quotient.mkₐ 𝒪 𝔪) := by
          rw [Algebra.map_top, eq_comm, AlgHom.range_eq_top]; apply Ideal.Quotient.mkₐ_surjective 𝒪 𝔪
        rw [h1, ← hG, AlgHom.map_adjoin]
        refine Algebra.adjoin_le ?_
        rintro _ ⟨g, hg, rfl⟩
        have : Ideal.Quotient.mkₐ 𝒪 𝔪 g = algebraMap 𝒪 (B ⧸ 𝔪) (c g) := by
          rw [Ideal.Quotient.mkₐ_eq_mk, IsScalarTower.algebraMap_apply 𝒪 B (B ⧸ 𝔪), Ideal.Quotient.algebraMap_eq,
            Ideal.Quotient.eq]
          exact h𝔪 g hg
        rw [this]; exact Subalgebra.algebraMap_mem _ _
      intro z
      have hz : z ∈ (⊥ : Subalgebra 𝒪 (B ⧸ 𝔪)) := hbot Algebra.mem_top
      rwa [Algebra.mem_bot] at hz
    obtain ⟨ψi, hψi, hsi⟩ := key (S.𝔪 i) hc
    obtain ⟨ψj, hψj, hsj⟩ := key (S.𝔪 j) hall
    have mkres : ∀ (𝔪 : Ideal B) [𝔪.IsMaximal], Function.Surjective (algebraMap 𝒪 (B ⧸ 𝔪)) →
        ∃ χ : B →ₐ[𝒪] ResidueField 𝒪, RingHom.ker χ.toRingHom = 𝔪 ∧
          ∀ (b : B) (a : 𝒪), Ideal.Quotient.mk 𝔪 b = algebraMap 𝒪 (B ⧸ 𝔪) a → χ b = residue 𝒪 a := by
      intro 𝔪 _ hs
      let := Ideal.Quotient.field 𝔪
      have hk : RingHom.ker (algebraMap 𝒪 (B ⧸ 𝔪)) = maximalIdeal 𝒪 :=
        IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hs)
      let e : ResidueField 𝒪 ≃+* B ⧸ 𝔪 :=
        (Ideal.quotEquivOfEq hk.symm).trans (RingHom.quotientKerEquivOfSurjective hs)
      have he : ∀ a : 𝒪, e (residue 𝒪 a) = algebraMap 𝒪 (B ⧸ 𝔪) a := fun a => rfl
      let χ₀ : B →+* ResidueField 𝒪 := e.symm.toRingHom.comp (Ideal.Quotient.mk 𝔪)
      have hχ₀ : ∀ a : 𝒪, χ₀ (algebraMap 𝒪 B a) = residue 𝒪 a := by
        intro a
        show e.symm (Ideal.Quotient.mk 𝔪 (algebraMap 𝒪 B a)) = residue 𝒪 a
        rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply, ← he, RingEquiv.symm_apply_apply]
      refine ⟨{ χ₀ with commutes' := hχ₀ }, ?_, ?_⟩
      ·
        ext b
        simp only [RingHom.mem_ker]
        show e.symm (Ideal.Quotient.mk 𝔪 b) = 0 ↔ b ∈ 𝔪
        rw [map_eq_zero_iff _ e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
      ·
        intro b a hba
        show e.symm (Ideal.Quotient.mk 𝔪 b) = residue 𝒪 a
        rw [hba, ← he, RingEquiv.symm_apply_apply]
    obtain ⟨χi, hki, hχi⟩ := mkres (S.𝔪 i) hsi
    obtain ⟨χj, hkj, hχj⟩ := mkres (S.𝔪 j) hsj
    have heq : χi = χj := by
      refine AlgHom.ext_of_adjoin_eq_top hG fun g hg => ?_
      have hgi : Ideal.Quotient.mk (S.𝔪 i) g = algebraMap 𝒪 (B ⧸ S.𝔪 i) (c g) := by
        rw [IsScalarTower.algebraMap_apply 𝒪 B (B ⧸ S.𝔪 i), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]
        exact hc g hg
      have hgj : Ideal.Quotient.mk (S.𝔪 j) g = algebraMap 𝒪 (B ⧸ S.𝔪 j) (c g) := by
        rw [IsScalarTower.algebraMap_apply 𝒪 B (B ⧸ S.𝔪 j), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]
        exact hall g hg
      rw [hχi g (c g) hgi, hχj g (c g) hgj]
    have : S.𝔪 i = S.𝔪 j := by rw [← hki, ← hkj, heq]
    exact hj (S.𝔪_injective this).symm
  have hstab : ∀ (b : B) (k : ℕ) (w : V), w ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V) →
      b • w ∈ ((maximalIdeal 𝒪) ^ k • ⊤ : Submodule 𝒪 V) := by
    intro b k w hw
    refine Submodule.smul_induction_on hw ?_ ?_
    ·
      intro a ha u _
      rw [smul_comm]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    ·
      intro u u' hu hu'
      rw [smul_add]; exact Submodule.add_mem _ hu hu'
  have hzero : ∀ j : Fin S.n, j ≠ i → S.e j • v = 0 := by
    intro j hj
    obtain ⟨g, hg, hgj⟩ := hsep_gen j hj
    obtain ⟨t, ht⟩ := exists_mul_mul_eq_of_notMem (S.idem j) (S.𝔪 j) (S.mem_of_isMaximal_of_ne j) hgj
    have hpow : ∀ n : ℕ, (t * x g) ^ n * S.e j = S.e j := by
      intro n
      induction n with
      | zero => rw [pow_zero, one_mul]
      | succ n ih => rw [pow_succ, mul_assoc, ht, ih]
    apply hsep
    intro k
    obtain ⟨n, hn⟩ := hv g hg k
    have : S.e j • v = (t ^ n * S.e j) • ((x g) ^ n • v) := by
      rw [← mul_smul, mul_assoc, mul_comm (S.e j), ← mul_assoc, ← mul_pow, hpow]
    rw [this]
    exact hstab _ k _ hn
  have hsum : (∑ j, S.e j) • v = S.e i • v := by
    rw [Finset.sum_smul, Finset.sum_eq_single i (fun j _ hj => hzero j hj) (fun h => (h (Finset.mem_univ i)).elim)]
  rw [S.coi.complete, one_smul] at hsum
  exact ⟨v, hsum.symm⟩


-- created on 2026-10-23
