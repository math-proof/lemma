import Mathlib.RingTheory.Noetherian.Nilpotent
import sympy.algebra.adic_completion.ring_functoriality

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

noncomputable def quotientPowEquivPiSup [IsArtinianRing (S ⧸ I)] {c n : ℕ}
    (hc : I.radical ^ c ≤ I ^ n) :
    (S ⧸ I ^ n) ≃+*
      ∀ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, S ⧸ (I ^ n ⊔ (P : Ideal S) ^ c) :=
  have := finite_setOf_isMaximal_and_le I
  (Ideal.quotEquivOfEq (iInf_sup_pow_eq I hc).symm).trans
    (Ideal.quotientInfRingEquivPiQuotient _ fun _ _ hPQ => isCoprime_sup_pow_of_ne I hPQ)

theorem quotientPowEquivPiSup_mk [IsArtinianRing (S ⧸ I)] {c n : ℕ}
    (hc : I.radical ^ c ≤ I ^ n) (x : S) :
    quotientPowEquivPiSup I hc (Ideal.Quotient.mk _ x) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
        Ideal.Quotient.mk (I ^ n ⊔ (P : Ideal S) ^ c) x := by
  funext _P
  simp [quotientPowEquivPiSup, Ideal.quotientInfRingEquivPiQuotient,
    Ideal.quotientInfToPiQuotient]

end Ideal

section Assembly

namespace AdicCompletion

variable {S : Type u₁} [CommRing S] (I : Ideal S)

theorem map_algHom_id_le {P : Ideal S} (hIP : I ≤ P) :
    I.map (AlgHom.id S S) ≤ P := by
  simp [hIP]

noncomputable def semilocalComponent {P : Ideal S} (hIP : I ≤ P) :
    AdicCompletion I S →ₐ[S] AdicCompletion P S :=
  mapₐ I P (AlgHom.id S S) (map_algHom_id_le I hIP)

theorem semilocalComponent_of {P : Ideal S} (hIP : I ≤ P) (x : S) :
    semilocalComponent I hIP (of I S x) = of P S x := by
  simp [semilocalComponent]

noncomputable def semilocalPiHom :
    AdicCompletion I S →+*
      ∀ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, AdicCompletion (P : Ideal S) S :=
  RingHom.pi fun P => (semilocalComponent I P.2.2).toRingHom

theorem semilocalPiHom_apply (x : AdicCompletion I S)
    (P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}) :
    semilocalPiHom I x P = semilocalComponent I P.2.2 x := rfl

theorem semilocalPiHom_of (x : S) :
    semilocalPiHom I (of I S x) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} => of (P : Ideal S) S x := by
  funext P
  exact semilocalComponent_of I P.2.2 x

theorem pow_smul_top_eq (n : ℕ) : (I ^ n • ⊤ : Ideal S) = I ^ n := by
  ext x; simp

noncomputable def ofCompatibleFamily (z : ∀ n, S ⧸ I ^ n)
    (hz : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (z n) = z m) :
    AdicCompletion I S :=
  ⟨fun n => Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n).symm (z n), by
    intro m n hmn
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z n)
    have hzm : z m = Ideal.Quotient.mk (I ^ m) r := by
      rw [← hz hmn, ← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    show transitionMap I S hmn (Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n).symm (z n)) =
      Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I m).symm (z m)
    rw [← hr, hzm, Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]
    rfl⟩

theorem evalₐ_ofCompatibleFamily (z : ∀ n, S ⧸ I ^ n)
    (hz : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (z n) = z m) (n : ℕ) :
    evalₐ I n (ofCompatibleFamily I z hz) = z n := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z n)
  rw [← hr]
  show Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n)
      (eval I S n (ofCompatibleFamily I z hz)) = Ideal.Quotient.mk (I ^ n) r
  rw [show eval I S n (ofCompatibleFamily I z hz) =
      Ideal.quotientEquivAlgOfEq S (pow_smul_top_eq I n).symm (z n) from rfl,
    ← hr, Ideal.quotientEquivAlgOfEq_mk, Ideal.quotientEquivAlgOfEq_mk]

variable [IsNoetherianRing S] [IsArtinianRing (S ⧸ I)]

omit [IsArtinianRing (S ⧸ I)] in

theorem exists_uniform_exponent :
    ∃ c₁ : ℕ, (∀ n : ℕ, I.radical ^ (c₁ * n) ≤ I ^ n) ∧ (∀ n : ℕ, n ≤ c₁ * n) := by
  obtain ⟨c₀, hc₀⟩ := Ideal.exists_radical_pow_le_of_fg I (IsNoetherian.noetherian _)
  refine ⟨c₀ + 1, fun n => ?_, fun n => Nat.le_mul_of_pos_left n c₀.succ_pos⟩
  rw [pow_mul]
  refine Ideal.pow_right_mono ?_ n
  rw [pow_succ]
  exact le_trans Ideal.mul_le_left hc₀

theorem semilocalPiHom_injective : Function.Injective (semilocalPiHom I) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
  refine ext_evalₐ fun n => ?_
  have hz : evalₐ I n (0 : AdicCompletion I S) = 0 := by simp
  rw [hz]
  obtain ⟨c₁, hrad, hle⟩ := exists_uniform_exponent I
  refine (Ideal.quotientPowEquivPiSup I (hrad n)).injective ?_
  change Ideal.quotientPowEquivPiSup I (hrad n) (evalₐ I n x) = 0
  funext P
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I (c₁ * n) x)
  have hev : evalₐ I n x = Ideal.Quotient.mk (I ^ n) r := by
    rw [← factorPow_evalₐ I (hle n) x, ← hr, Ideal.Quotient.factorPow,
      Ideal.Quotient.factor_mk]
  have hP0 : evalₐ (P : Ideal S) (c₁ * n) (semilocalPiHom I x P) = 0 := by
    simp [congrFun hx P]
  rw [semilocalPiHom_apply, semilocalComponent, evalₐ_mapₐ, ← hr, levelMapₐ_mk] at hP0
  have hrP : r ∈ (P : Ideal S) ^ (c₁ * n) := by
    rwa [AlgHom.coe_id, id_eq, Ideal.Quotient.eq_zero_iff_mem] at hP0
  rw [hev, Ideal.quotientPowEquivPiSup_mk, Pi.zero_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right hrP)

omit [IsNoetherianRing S] in

theorem quotientPowEquivPiSup_factorPow {c n c' n' : ℕ}
    (hc : I.radical ^ c ≤ I ^ n) (hc' : I.radical ^ c' ≤ I ^ n')
    (hn : n ≤ n') (hcc : c ≤ c') (z : S ⧸ I ^ n') :
    Ideal.quotientPowEquivPiSup I hc (Ideal.Quotient.factorPow I hn z) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
        Ideal.Quotient.factor
          (sup_le_sup (Ideal.pow_le_pow_right hn) (Ideal.pow_le_pow_right hcc))
          (Ideal.quotientPowEquivPiSup I hc' z P) := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective z
  funext P
  rw [← hr, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk,
    Ideal.quotientPowEquivPiSup_mk, Ideal.quotientPowEquivPiSup_mk,
    Ideal.Quotient.factor_mk]

theorem semilocalPiHom_surjective : Function.Surjective (semilocalPiHom I) := by
  intro y
  obtain ⟨c₁, hrad, hle⟩ := exists_uniform_exponent I
  have hmono : ∀ {m n : ℕ}, m ≤ n → c₁ * m ≤ c₁ * n := fun h => Nat.mul_le_mul_left _ h

  set z : ∀ n, S ⧸ I ^ n := fun n =>
    (Ideal.quotientPowEquivPiSup I (hrad n)).symm
      (fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
        Ideal.Quotient.factor le_sup_right (evalₐ (P : Ideal S) (c₁ * n) (y P)))
    with hz_def
  have hz : ∀ {m n : ℕ} (h : m ≤ n), Ideal.Quotient.factorPow I h (z n) = z m := by
    intro m n hmn
    refine (Ideal.quotientPowEquivPiSup I (hrad m)).injective ?_
    rw [RingEquiv.apply_symm_apply,
      quotientPowEquivPiSup_factorPow I (hrad m) (hrad n) hmn (hmono hmn),
      RingEquiv.apply_symm_apply]
    funext P
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ (P : Ideal S) (c₁ * n) (y P))
    have hsm : evalₐ (P : Ideal S) (c₁ * m) (y P) =
        Ideal.Quotient.mk ((P : Ideal S) ^ (c₁ * m)) s := by
      rw [← factorPow_evalₐ (P : Ideal S) (hmono hmn) (y P), ← hs,
        Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    rw [← hs, hsm, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
      Ideal.Quotient.factor_mk]
  refine ⟨ofCompatibleFamily I z hz, ?_⟩
  funext P
  refine ext_evalₐ fun k => ?_

  rw [semilocalPiHom_apply, semilocalComponent, evalₐ_mapₐ, evalₐ_ofCompatibleFamily]

  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (z k)
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (evalₐ (P : Ideal S) (c₁ * k) (y P))
  have hcomp : Ideal.Quotient.mk (I ^ k ⊔ (P : Ideal S) ^ (c₁ * k)) r =
      Ideal.Quotient.mk (I ^ k ⊔ (P : Ideal S) ^ (c₁ * k)) s := by
    have hzk : Ideal.quotientPowEquivPiSup I (hrad k) (z k) P =
        Ideal.Quotient.factor le_sup_right (evalₐ (P : Ideal S) (c₁ * k) (y P)) :=
      congrFun ((Ideal.quotientPowEquivPiSup I (hrad k)).apply_symm_apply
        (fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} =>
          Ideal.Quotient.factor le_sup_right (evalₐ (P : Ideal S) (c₁ * k) (y P)))) P
    have hzk' : Ideal.quotientPowEquivPiSup I (hrad k) (z k) P =
        Ideal.Quotient.mk (I ^ k ⊔ (P : Ideal S) ^ (c₁ * k)) r := by
      rw [← hr, Ideal.quotientPowEquivPiSup_mk]
    rw [← hzk', hzk, ← hs, Ideal.Quotient.factor_mk]
  have hrs : r - s ∈ (P : Ideal S) ^ k := by
    have hmem : r - s ∈ I ^ k ⊔ (P : Ideal S) ^ (c₁ * k) :=
      (Ideal.Quotient.eq).mp hcomp
    exact Ideal.sup_pow_le_pow_of_le I P.2.2 (hle k) hmem
  rw [← hr, levelMapₐ_mk, AlgHom.coe_id, id_eq,
    ← factorPow_evalₐ (P : Ideal S) (hle k) (y P), ← hs,
    Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  exact (Ideal.Quotient.eq).mpr hrs

noncomputable def semilocalPiEquiv :
    AdicCompletion I S ≃+*
      ∀ P : {P : Ideal S // P.IsMaximal ∧ I ≤ P}, AdicCompletion (P : Ideal S) S :=
  RingEquiv.ofBijective (semilocalPiHom I)
    ⟨semilocalPiHom_injective I, semilocalPiHom_surjective I⟩

theorem semilocalPiEquiv_of (x : S) :
    semilocalPiEquiv I (of I S x) =
      fun P : {P : Ideal S // P.IsMaximal ∧ I ≤ P} => of (P : Ideal S) S x :=
  semilocalPiHom_of I x

theorem semilocalPiEquiv_apply {𝔫 : Ideal S} [h𝔫 : 𝔫.IsMaximal] (hI : I ≤ 𝔫)
    (y : AdicCompletion I S) :
    semilocalPiEquiv I y ⟨𝔫, h𝔫, hI⟩ = semilocalComponent I hI y :=
  semilocalPiHom_apply I y ⟨𝔫, h𝔫, hI⟩

end AdicCompletion

end Assembly
