import Mathlib.RingTheory.Noetherian.Nilpotent
import Theorem.Algebra.AdicCompletion.RingFunctoriality.Part7
universe u₁ u₂


section ArtinianDevice

variable {S : Type u₁} [CommRing S]

theorem isArtinian_of_finite_of_smul_eq_zero (I : Ideal S) [IsArtinianRing (S ⧸ I)]
    {M : Type u₂} [AddCommGroup M] [Module S M] [Module.Finite S M]
    (hann : ∀ i ∈ I, ∀ m : M, i • m = (0 : M)) : IsArtinian S M := by
  have hSI : IsArtinian S (S ⧸ I) :=
    isArtinian_of_surjective_algebraMap (R := S ⧸ I) (M := S ⧸ I)
      (by rw [Ideal.Quotient.algebraMap_eq]; exact Ideal.Quotient.mk_surjective)
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := S) (M := M)

  have hker : ∀ i : Fin k, (I : Submodule S S) ≤
      LinearMap.ker (LinearMap.toSpanSingleton S M (s i)) := by
    intro i r hr
    simpa using hann r hr (s i)
  let ψ : ∀ _ : Fin k, (S ⧸ I) →ₗ[S] M :=
    fun i => Submodule.liftQ _ (LinearMap.toSpanSingleton S M (s i)) (hker i)
  let φ : (Fin k → S ⧸ I) →ₗ[S] M := LinearMap.lsum S (fun _ : Fin k => S ⧸ I) ℕ ψ
  have hφ : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hs, Submodule.span_le]
    rintro - ⟨i, rfl⟩
    refine ⟨Pi.single i (1 : S ⧸ I), ?_⟩
    simp only [φ, LinearMap.lsum_apply, LinearMap.coe_sum, Finset.sum_apply,
      LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i]
    · simp only [ψ, Pi.single_eq_same]
      rw [show (1 : S ⧸ I) = Submodule.Quotient.mk (1 : S) from rfl, Submodule.liftQ_apply]
      simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb, ψ]
    · simp
  exact isArtinian_of_surjective _ φ hφ

end ArtinianDevice

namespace Ideal

variable {S : Type u₁} [CommRing S]

theorem isArtinianRing_quotient_pow [IsNoetherianRing S] (I : Ideal S)
    [IsArtinianRing (S ⧸ I)] (n : ℕ) : IsArtinianRing (S ⧸ I ^ n) := by
  suffices h : IsArtinian S (S ⧸ I ^ n) by
    exact isArtinian_of_tower S h
  induction n with
  | zero =>
    have : Subsingleton (S ⧸ I ^ 0) :=
      ⟨fun a b => Quotient.inductionOn₂' a b fun x y =>
        Ideal.Quotient.eq.mpr (by simp [pow_zero, Ideal.one_eq_top])⟩
    infer_instance
  | succ n ih =>
    have := ih

    let q : (S ⧸ I ^ (n + 1)) →ₗ[S] S ⧸ I ^ n :=
      Submodule.factor (by
        exact_mod_cast Ideal.pow_le_pow_right (Nat.le_succ n))
    have : IsArtinian S (LinearMap.ker q) := by
      refine isArtinian_of_finite_of_smul_eq_zero I (fun i hi => ?_)
      rintro ⟨x, hx⟩
      refine Subtype.ext ?_
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
      have hr : r ∈ I ^ n := by
        simpa [q, Ideal.Quotient.eq_zero_iff_mem] using hx
      show i • Ideal.Quotient.mk (I ^ (n + 1)) r = 0
      have hmk : i • Ideal.Quotient.mk (I ^ (n + 1)) r =
          Ideal.Quotient.mk (I ^ (n + 1)) (i * r) := rfl
      rw [hmk, Ideal.Quotient.eq_zero_iff_mem, pow_succ']
      exact Ideal.mul_mem_mul hi hr
    exact isArtinian_of_range_eq_ker (LinearMap.ker q).subtype q (Submodule.range_subtype _)

variable (I : Ideal S)

theorem isMaximal_of_isPrime_of_le [IsArtinianRing (S ⧸ I)] (Q : Ideal S) [hQ : Q.IsPrime]
    (hIQ : I ≤ Q) : Q.IsMaximal := by
  have : (Q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hIQ)
  have : (Q.map (Ideal.Quotient.mk I)).IsMaximal :=
    IsArtinianRing.isMaximal_of_isPrime _
  have hQc : Q = (Q.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact (sup_eq_left.mpr hIQ).symm
  rw [hQc]
  exact Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective

theorem finite_setOf_isMaximal_and_le [IsArtinianRing (S ⧸ I)] :
    Finite {P : Ideal S // P.IsMaximal ∧ I ≤ P} := by
  refine Finite.of_surjective
    (f := fun Q : MaximalSpectrum (S ⧸ I) =>
      (⟨Q.asIdeal.comap (Ideal.Quotient.mk I),
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective,
        by simpa [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] using
          Ideal.ker_le_comap (Ideal.Quotient.mk I)⟩ :
        {P : Ideal S // P.IsMaximal ∧ I ≤ P})) ?_
  rintro ⟨P, hP, hIP⟩
  refine ⟨⟨P.map (Ideal.Quotient.mk I), ?_⟩, ?_⟩
  · have : (P.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
        (by rw [Ideal.mk_ker]; exact hIP)
    exact IsArtinianRing.isMaximal_of_isPrime _
  · refine Subtype.ext ?_
    show (P.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) = P
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_eq_left.mpr hIP

theorem prod_pow_le_pow_of_radical_pow_le [IsArtinianRing (S ⧸ I)]
    {c n : ℕ} (hc : I.radical ^ c ≤ I ^ n) (s : Finset {P : Ideal S // P.IsMaximal ∧ I ≤ P})
    (hs : ∀ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, P ∈ s) :
    (∏ P ∈ s, (P : Ideal S) ^ c) ≤ I ^ n := by
  have hprodrad : (∏ P ∈ s, (P : Ideal S)) ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro Q ⟨hIQ, hQprime⟩
    have := hQprime
    have hQmax : Q.IsMaximal := isMaximal_of_isPrime_of_le I Q hIQ
    exact le_trans Ideal.prod_le_inf (Finset.inf_le (hs ⟨Q, hQmax, hIQ⟩))
  calc (∏ P ∈ s, (P : Ideal S) ^ c)
      = (∏ P ∈ s, (P : Ideal S)) ^ c := Finset.prod_pow s c _
    _ ≤ I.radical ^ c := Ideal.pow_right_mono hprodrad c
    _ ≤ I ^ n := hc

theorem sup_pow_le_pow_of_le {P : Ideal S} (hIP : I ≤ P) {m n : ℕ} (hnm : n ≤ m) :
    I ^ n ⊔ P ^ m ≤ P ^ n :=
  sup_le (Ideal.pow_right_mono hIP n) (Ideal.pow_le_pow_right hnm)

theorem sup_mul_sup_le (A B C : Ideal S) : (A ⊔ B) * (A ⊔ C) ≤ A ⊔ B * C := by
  rw [Ideal.mul_sup, Ideal.sup_mul, Ideal.sup_mul]
  refine sup_le (sup_le ?_ ?_) (sup_le ?_ ?_)
  · exact le_trans Ideal.mul_le_left le_sup_left
  · exact le_trans Ideal.mul_le_right le_sup_left
  · exact le_trans Ideal.mul_le_left le_sup_left
  · exact le_sup_right

theorem isCoprime_sup_pow_of_ne [IsArtinianRing (S ⧸ I)] {c n : ℕ}
    {P Q : {P : Ideal S // P.IsMaximal ∧ I ≤ P}} (hPQ : P ≠ Q) :
    IsCoprime (I ^ n ⊔ (P : Ideal S) ^ c) (I ^ n ⊔ (Q : Ideal S) ^ c) := by
  have hPQ' : (⟨(P : Ideal S), P.2.1⟩ : MaximalSpectrum S) ≠ ⟨(Q : Ideal S), Q.2.1⟩ := by
    intro h
    exact hPQ (Subtype.ext (congrArg MaximalSpectrum.asIdeal h))
  have h1 : IsCoprime ((P : Ideal S) ^ c) ((Q : Ideal S) ^ c) :=
    (MaximalSpectrum.isCoprime_of_ne hPQ').pow
  rw [Ideal.isCoprime_iff_sup_eq] at h1 ⊢
  rw [eq_top_iff, ← h1]
  exact sup_le (le_trans le_sup_right le_sup_left) (le_sup_of_le_right le_sup_right)

theorem iInf_sup_pow_eq [IsArtinianRing (S ⧸ I)] {c n : ℕ} (hc : I.radical ^ c ≤ I ^ n) :
    ⨅ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, (I ^ n ⊔ (P : Ideal S) ^ c) = I ^ n := by
  refine le_antisymm ?_ (le_iInf fun P => le_sup_left)
  by_cases hI : I = ⊤
  · subst hI
    simp [Ideal.top_pow]
  · have := finite_setOf_isMaximal_and_le I
    have := Fintype.ofFinite {P : Ideal S // P.IsMaximal ∧ I ≤ P}
    classical
    have key : ∀ t : Finset {P : Ideal S // P.IsMaximal ∧ I ≤ P},
        (⨅ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, (I ^ n ⊔ (P : Ideal S) ^ c)) ≤
          I ^ n ⊔ ∏ P ∈ t, (P : Ideal S) ^ c := by
      intro t
      induction t using Finset.induction_on with
      | empty => simp
      | insert Q t hQt ih =>
        have hcop : IsCoprime (I ^ n ⊔ ∏ P ∈ t, (P : Ideal S) ^ c)
            (I ^ n ⊔ (Q : Ideal S) ^ c) := by
          have hfac : IsCoprime (∏ P ∈ t, (P : Ideal S) ^ c) ((Q : Ideal S) ^ c) := by
            refine IsCoprime.prod_left fun P hPt => ?_
            have hPQ : P ≠ Q := fun h => hQt (h ▸ hPt)
            have hPQ' : (⟨(P : Ideal S), P.2.1⟩ : MaximalSpectrum S) ≠
                ⟨(Q : Ideal S), Q.2.1⟩ := by
              intro h
              exact hPQ (Subtype.ext (congrArg MaximalSpectrum.asIdeal h))
            exact (MaximalSpectrum.isCoprime_of_ne hPQ').pow
          rw [Ideal.isCoprime_iff_sup_eq] at hfac ⊢
          rw [eq_top_iff, ← hfac]
          exact sup_le (le_trans le_sup_right le_sup_left) (le_sup_of_le_right le_sup_right)
        calc (⨅ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, (I ^ n ⊔ (P : Ideal S) ^ c))
            ≤ (I ^ n ⊔ ∏ P ∈ t, (P : Ideal S) ^ c) ⊓ (I ^ n ⊔ (Q : Ideal S) ^ c) :=
              le_inf ih (iInf_le _ Q)
          _ = (I ^ n ⊔ ∏ P ∈ t, (P : Ideal S) ^ c) * (I ^ n ⊔ (Q : Ideal S) ^ c) :=
              (Ideal.mul_eq_inf_of_isCoprime hcop).symm
          _ ≤ I ^ n ⊔ (∏ P ∈ t, (P : Ideal S) ^ c) * (Q : Ideal S) ^ c :=
              sup_mul_sup_le _ _ _
          _ = I ^ n ⊔ ∏ P ∈ insert Q t, (P : Ideal S) ^ c := by
              rw [Finset.prod_insert hQt, mul_comm]
    refine le_trans (key Finset.univ) ?_
    refine sup_le le_rfl ?_
    exact prod_pow_le_pow_of_radical_pow_le I hc Finset.univ fun P => Finset.mem_univ P

end Ideal
