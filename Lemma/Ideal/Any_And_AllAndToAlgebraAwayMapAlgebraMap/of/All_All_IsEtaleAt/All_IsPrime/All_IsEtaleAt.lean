import Mathlib
import Initialize.Tactic.Attr.Basic
open PrimeSpectrum


/--
[Algebra_exists_etale_localizationAway_of_forall_isEtaleAt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_etale_localizationAway_of_forall_isEtaleAt.lean)
-/
@[path]
private lemma main
  {R S : Type u} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S] [Module.Finite R S] [Algebra.FinitePresentation R S]
  {T : Finset (Ideal R)}
-- given
  (hgen : ∀ (q : Ideal S) [q.IsPrime], q.comap (algebraMap R S) = ⊥ → Algebra.IsEtaleAt R q)
  (hT : ∀ p ∈ T, p.IsPrime)
  (hTet : ∀ p ∈ T, ∀ (q : Ideal S) [q.IsPrime], q.comap (algebraMap R S) = p → Algebra.IsEtaleAt R q) :
-- imply
  ∃ c : R, c ≠ 0 ∧ (∀ p ∈ T, c ∉ p) ∧
    letI := (Localization.awayMap (algebraMap R S) c).toAlgebra
    Algebra.Etale (Localization.Away c) (Localization.Away (algebraMap R S c)) := by
-- proof
  classical
  set Z : Set (PrimeSpectrum S) := (Algebra.etaleLocus R S)ᶜ with hZ
  have hZc : IsClosed Z := Algebra.isOpen_etaleLocus.isClosed_compl
  set W : Set (PrimeSpectrum R) := comap (algebraMap R S) '' Z with hW
  have hWc : IsClosed W :=
    isClosedMap_comap_of_isIntegral (algebraMap R S) (fun x => Algebra.IsIntegral.isIntegral (R := R) x) Z hZc
  set I : Ideal R := vanishingIdeal W with hI
  have hWI : zeroLocus (I : Set R) = W := by
    rw [hI, zeroLocus_vanishingIdeal_eq_closure, hWc.closure_eq]
  have key : ∀ (p : Ideal R) [p.IsPrime],
      (∀ (q : Ideal S) [q.IsPrime], q.comap (algebraMap R S) = p → Algebra.IsEtaleAt R q) → ¬ I ≤ p := by
    intro p _ hp hIp
    have hmem : (⟨p, inferInstance⟩ : PrimeSpectrum R) ∈ zeroLocus (I : Set R) := hIp
    rw [hWI] at hmem
    obtain ⟨q, hqZ, hq⟩ := hmem
    apply hqZ
    apply hp q.asIdeal (congrArg PrimeSpectrum.asIdeal hq)
  have havoid : ¬ ((I : Set R) ⊆ ⋃ p ∈ (↑(insert (⊥ : Ideal R) T) : Set (Ideal R)), ((p : Ideal R) : Set R)) := by
    have hprime : ∀ p ∈ insert (⊥ : Ideal R) T, p ≠ ⊥ → p ≠ ⊥ → p.IsPrime := by
      intro p hp _ _
      obtain rfl | hpT := Finset.mem_insert.mp hp
      ·
        apply Ideal.isPrime_bot
      ·
        apply hT p hpT
    rw [Ideal.subset_union_prime (⊥ : Ideal R) (⊥ : Ideal R) hprime]
    rintro ⟨p, hp, hIp⟩
    obtain rfl | hpT := Finset.mem_insert.mp hp
    ·
      apply key ⊥ (fun q _ hq => hgen q hq) hIp
    ·
      let _ := hT p hpT
      apply key p (fun q _ hq => hTet p hpT q hq) hIp
  rw [Set.not_subset] at havoid
  obtain ⟨c, hcI, hc⟩ := havoid
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists, Finset.coe_insert, Set.mem_insert_iff] at hc
  have hc0 : c ≠ 0 := fun h0 => hc ⊥ (Or.inl rfl) (by rw [h0]; apply Ideal.zero_mem)
  have hcT : ∀ p ∈ T, c ∉ p := fun p hp => hc p (Or.inr hp)
  refine ⟨c, hc0, hcT, ?_⟩
  have hsub : ↑(basicOpen (algebraMap R S c)) ⊆ Algebra.etaleLocus R S := by
    intro q hq
    by_contra hqZ
    have hW' : comap (algebraMap R S) q ∈ W := ⟨q, hqZ, rfl⟩
    rw [← hWI] at hW'
    apply hq (hW' hcI)
  let _ : Algebra.Etale R (Localization.Away (algebraMap R S c)) :=
    Algebra.basicOpen_subset_etaleLocus_iff_etale.mp hsub
  let _ := (Localization.awayMap (algebraMap R S) c).toAlgebra
  let _ : IsScalarTower R (Localization.Away c) (Localization.Away (algebraMap R S c)) :=
    IsScalarTower.of_algebraMap_eq' (by rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_comp, ← IsScalarTower.algebraMap_eq])
  let _ : IsLocalization ((Submonoid.powers c).map (algebraMap R S)) (Localization.Away (algebraMap R S c)) := by
    rw [Submonoid.map_powers]
    apply Localization.isLocalization
  let _ : Algebra.FormallyEtale (Localization.Away c) (Localization.Away (algebraMap R S c)) :=
    Algebra.FormallyEtale.localization_base (Submonoid.powers c)
  let _ : Algebra.Etale R (Localization.Away c) := Algebra.Etale.of_isLocalizationAway c
  let _ : Algebra.FinitePresentation (Localization.Away c) (Localization.Away (algebraMap R S c)) :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ _
  refine ⟨inferInstance, inferInstance⟩


-- created on 2026-10-13
