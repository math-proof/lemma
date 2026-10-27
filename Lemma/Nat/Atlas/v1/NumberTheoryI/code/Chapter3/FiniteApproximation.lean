import Mathlib
import Initialize.Tactic.Attr.Basic
open UniqueFactorizationMonoid IsDedekindDomain Ideal Finset


/--
[Finset.prod_ideal_ne_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/FiniteApproximation.lean)
-/
@[path]
lemma Finset.prod_ideal_ne_bot
  [CommRing A]
  [IsDomain A]
  {s : Finset ι}
  {f : ι → Ideal A}
-- given
  (hf : ∀ i ∈ s, f i ≠ ⊥) :
-- imply
  ∏ i ∈ s, f i ≠ ⊥ := by
-- proof
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s' hna ih =>
    rw [Finset.prod_cons]
    exact mul_ne_zero (hf a (Finset.mem_cons_self a s'))
      (ih (fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi))))
variable {A : Type*} [CommRing A] [IsDomain A] [IsDedekindDomain A]

/--
[Ideal.exists_elem_eq_valuation_at_primes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Chapter3/FiniteApproximation.lean)
-/
@[path]
lemma Ideal.exists_elem_eq_valuation_at_primes
  [CommRing A]
  [IsDomain A]
  [IsDedekindDomain A]
  {s : Finset ι}
  {ps : ι → HeightOneSpectrum A}
  {I : Ideal A}
-- given
  (hI : I ≠ ⊥) :
-- imply
  ∃ x ∈ I, x ≠ (0 : A) ∧ ∀ i ∈ s, let e := Multiset.count (normalize (ps i).asIdeal) (normalizedFactors I) x ∈ (ps i).asIdeal ^ e ∧ x ∉ (ps i).asIdeal ^ (e + 1) := by
-- proof
  classical
  obtain rfl | hs := s.eq_empty_or_nonempty
  · obtain ⟨x, hx, hx_ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    exact ⟨x, hx, hx_ne, fun _ h => absurd h (Finset.notMem_empty _)⟩
  have hle : I * ∏ i ∈ s, (ps i).asIdeal ≤ I := by
    calc I * ∏ i ∈ s, (ps i).asIdeal ≤ I * ⊤ := by gcongr; exact le_top
      _ = I := mul_top I
  have hne : I * ∏ i ∈ s, (ps i).asIdeal ≠ ⊥ :=
    mul_ne_zero hI (Finset.prod_ideal_ne_bot s _ (fun i _ => (ps i).ne_bot))
  obtain ⟨a, ha_sup⟩ := IsDedekindDomain.exists_sup_span_eq hle hne
  have hmem : a ∈ I :=
    (Ideal.span_le.trans Set.singleton_subset_iff).mp (ha_sup ▸ le_sup_right)
  have ha_ne : a ≠ 0 := by
    intro h
    rw [h, Ideal.span_singleton_eq_bot.mpr rfl, sup_bot_eq] at ha_sup
    obtain ⟨j, hj⟩ := hs
    have heq : I * ∏ i ∈ s, (ps i).asIdeal = I * ⊤ := by rw [ha_sup, mul_top]
    have htop : ∏ i ∈ s, (ps i).asIdeal = ⊤ := mul_left_cancel₀ hI heq
    have hle' : ∏ i ∈ s, (ps i).asIdeal ≤ (ps j).asIdeal := by
      rw [← Finset.mul_prod_erase s _ hj]; exact Ideal.mul_le_right
    exact (ps j).isPrime.ne_top (le_antisymm le_top (htop ▸ hle'))
  refine ⟨a, hmem, ha_ne, fun i hi => ?_⟩
  have hirr : Irreducible (ps i).asIdeal :=
    (Ideal.prime_of_isPrime (ps i).ne_bot (ps i).isPrime).irreducible
  set e := Multiset.count (normalize (ps i).asIdeal) (normalizedFactors I)
  have hI_le : I ≤ (ps i).asIdeal ^ e := by
    rw [← Ideal.dvd_iff_le, pow_dvd_iff_le_emultiplicity,
      emultiplicity_eq_count_normalizedFactors hirr hI]
  have hI_not_le : ¬(I ≤ (ps i).asIdeal ^ (e + 1)) := by
    rw [← Ideal.dvd_iff_le, pow_dvd_iff_le_emultiplicity,
      emultiplicity_eq_count_normalizedFactors hirr hI, not_le]
    exact_mod_cast Nat.lt_succ_iff.mpr le_rfl
  exact ⟨hI_le hmem, fun ha_in =>
    hI_not_le (ha_sup ▸ sup_le
      (show I * ∏ j ∈ s, (ps j).asIdeal ≤ (ps i).asIdeal ^ (e + 1) by
        rw [pow_succ]; gcongr
        rw [← Finset.mul_prod_erase s _ hi]; exact Ideal.mul_le_right)
      ((Ideal.span_le.trans Set.singleton_subset_iff).mpr ha_in))⟩


-- created on 2026-10-23
