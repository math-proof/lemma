import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.LocalExtensions.Part2
open Ideal Polynomial
open scoped Pointwise


/--
[nakayama_local_ring_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma nakayama_local_ring_generators
  [CommRing R]
  [IsLocalRing R]
  [AddCommGroup M]
  [Module R M]
  {N N' : Submodule R M}
-- given
  (hN' : N'.FG)
  (hNN : N' ≤ N ⊔ (IsLocalRing.maximalIdeal R) • N') :
-- imply
  N' ≤ N := by
-- proof
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hN'
  · rw [IsLocalRing.jacobson_eq_maximalIdeal]
    exact bot_ne_top
  · exact hNN

/--
[maximal_ideal_contains_image_of_finite_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma maximal_ideal_contains_image_of_finite_algebra
  [CommRing A]
  [IsLocalRing A]
  [IsNoetherianRing A]
  [CommRing B]
  [Algebra A B]
  [Module.Finite A B]
  {𝔪 : Ideal B}
  [h𝔪 : 𝔪.IsMaximal] :
-- imply
  Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≤ 𝔪 := by
-- proof
  by_contra h
  have h_sup : 𝔪 ⊔ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) = ⊤ := by
    apply h𝔪.1.2
    exact lt_of_le_of_ne le_sup_left (fun h' => h (h' ▸ le_sup_right))
  have h_sub : (⊤ : Submodule A B) ≤
    (𝔪.restrictScalars A) ⊔ (IsLocalRing.maximalIdeal A) • ⊤ := by
    rw [Ideal.smul_top_eq_map]
    intro b _
    have hb : b ∈ (𝔪 ⊔ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) : Ideal B) := by
      rw [h_sup]; trivial
    simp only [Submodule.mem_sup, Submodule.restrictScalars_mem] at hb ⊢
    obtain ⟨x, hx, y, hy, rfl⟩ := hb
    exact ⟨x, hx, y, hy, rfl⟩
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top ?_ h_sub
  · have : 𝔪 = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    exact hle trivial
    exact h𝔪.1.ne_top this
  · rw [IsLocalRing.jacobson_eq_maximalIdeal]
    exact bot_ne_top

/--
[Polynomial.comap_mapRingHom_bot_eq_map_C_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma Polynomial.comap_mapRingHom_bot_eq_map_C_ker
  [CommRing A]
  {I : Ideal A} :
-- imply
  Ideal.comap (Polynomial.mapRingHom (Ideal.Quotient.mk I)) ⊥ = Ideal.map Polynomial.C I := by
-- proof
  rw [← RingHom.ker_eq_comap_bot, Polynomial.ker_mapRingHom, mk_ker]

/--
[AdjoinRoot.maximal_ideal_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma AdjoinRoot.maximal_ideal_form
  [CommRing A]
  [IsLocalRing A]
  [IsNoetherianRing A]
  {g : Polynomial A}
  [hA : Module.Finite A (AdjoinRoot g)]
  {𝔪 : Ideal (AdjoinRoot g)}
  [h𝔪 : 𝔪.IsMaximal] :
-- imply
  ∃ (q : Polynomial A), Irreducible (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧ (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∣ (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧ 𝔪 = Ideal.map (algebraMap A (AdjoinRoot g)) (IsLocalRing.maximalIdeal A) ⊔ Ideal.span {AdjoinRoot.mk g q} := by
-- proof
  let pp := IsLocalRing.maximalIdeal A
  let pi : A →+* A ⧸ pp := Ideal.Quotient.mk pp
  letI : Field (A ⧸ pp) := Ideal.Quotient.field _
  let pB := Ideal.map (algebraMap A (AdjoinRoot g)) pp
  have hpB_le : pB ≤ 𝔪 := maximal_ideal_contains_image_of_finite_algebra 𝔪
  let MM := Ideal.comap (AdjoinRoot.mk g) 𝔪
  have hMM_max : MM.IsMaximal := Ideal.comap_isMaximal_of_surjective _ AdjoinRoot.mk_surjective
  have hker_mk : RingHom.ker (AdjoinRoot.mk g) ≤ MM := fun f hf =>
    show (AdjoinRoot.mk g) f ∈ 𝔪 from (RingHom.mem_ker.mp hf) ▸ 𝔪.zero_mem
  have hCp_le : Ideal.map Polynomial.C pp ≤ MM := by
    rw [Ideal.map_le_iff_le_comap]
    exact fun a ha => hpB_le (Ideal.mem_map_of_mem _ ha)
  have hker_map : Ideal.comap (Polynomial.mapRingHom pi) ⊥ ≤ MM := by
    rw [Polynomial.comap_mapRingHom_bot_eq_map_C_ker]; exact hCp_le
  let MMbar := Ideal.map (Polynomial.mapRingHom pi) MM
  haveI : MM.IsMaximal := hMM_max
  have hMMbar_max : MMbar.IsMaximal := by
    apply Ideal.IsMaximal.map_of_surjective_of_ker_le
      (Polynomial.map_surjective pi Ideal.Quotient.mk_surjective)
    rwa [RingHom.ker_eq_comap_bot]
  have hg_in : g ∈ MM := hker_mk (by rw [RingHom.mem_ker]; exact AdjoinRoot.mk_self)
  have hgbar_in : Polynomial.map pi g ∈ MMbar := Ideal.mem_map_of_mem _ hg_in
  obtain ⟨qb, hqb_irred, hMMbar_eq⟩ :
    ∃ qb : (A ⧸ pp)[X], Irreducible qb ∧ MMbar = span {qb} := by
    obtain ⟨⟨qb, hqb⟩⟩ := IsPrincipalIdealRing.principal MMbar
    refine ⟨qb, ?_, hqb⟩
    rw [hqb] at hMMbar_max
    have hqb0 : qb ≠ 0 := by
      intro h; subst h
      have h1 : ((A ⧸ pp)[X] ∙ (0 : (A ⧸ pp)[X])) = ⊥ := by simp
      rw [h1] at hMMbar_max
      exact Polynomial.not_isField (A ⧸ pp) (Ring.isField_iff_maximal_bot.mpr hMMbar_max)
    exact ((span_singleton_prime hqb0).mp hMMbar_max.isPrime).irreducible
  have hqb_dvd : qb ∣ Polynomial.map pi g := by
    rw [← mem_span_singleton, ← hMMbar_eq]; exact hgbar_in
  obtain ⟨q, hq_lift⟩ := Polynomial.map_surjective pi Ideal.Quotient.mk_surjective qb
  refine ⟨q, ?_, ?_, ?_⟩
  ·
    change Irreducible (Polynomial.map pi q); rwa [hq_lift]
  ·
    change Polynomial.map pi q ∣ Polynomial.map pi g; rwa [hq_lift]
  ·
    have hMM_comap : MM = Ideal.comap (Polynomial.mapRingHom pi) MMbar := by
      show MM = Ideal.comap (Polynomial.mapRingHom pi) (Ideal.map (Polynomial.mapRingHom pi) MM)
      rw [Ideal.comap_map_of_surjective _
        (Polynomial.map_surjective pi Ideal.Quotient.mk_surjective)]
      exact (sup_eq_left.mpr hker_map).symm
    have hMMbar_span : MMbar = Ideal.map (Polynomial.mapRingHom pi) (span {q}) := by
      rw [hMMbar_eq, Ideal.map_span, Set.image_singleton]
      simp only [Polynomial.coe_mapRingHom, hq_lift]
    have hMM_decomp : MM = span {q} ⊔ Ideal.map Polynomial.C pp := by
      rw [hMM_comap, hMMbar_span,
        Ideal.comap_map_of_surjective _
          (Polynomial.map_surjective pi Ideal.Quotient.mk_surjective),
        Polynomial.comap_mapRingHom_bot_eq_map_C_ker]
    have hmm_map : 𝔪 = Ideal.map (AdjoinRoot.mk g) MM :=
      (Ideal.map_comap_of_surjective _ AdjoinRoot.mk_surjective 𝔪).symm
    rw [hmm_map, hMM_decomp, Ideal.map_sup, Ideal.map_span, Set.image_singleton,
      Ideal.map_map, sup_comm]
    congr 1

/--
[AdjoinRoot.is_maximal_of_irreducible_factor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma AdjoinRoot.is_maximal_of_irreducible_factor
  [CommRing A]
  [IsLocalRing A]
  {g : Polynomial A}
  {q : Polynomial A}
-- given
  (hirr : Irreducible (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))))
  (hdvd : (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∣ (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A)))) :
-- imply
  (Ideal.map (algebraMap A (AdjoinRoot g)) (IsLocalRing.maximalIdeal A) ⊔ Ideal.span {AdjoinRoot.mk g q}).IsMaximal := by
-- proof
  let pp := IsLocalRing.maximalIdeal A
  let pi : A →+* A ⧸ pp := Ideal.Quotient.mk pp
  letI : Field (A ⧸ pp) := Ideal.Quotient.field _
  let M : Ideal A[X] := Ideal.span {q} ⊔ Ideal.map Polynomial.C pp
  have hqbar_max : (Ideal.span {Polynomial.map pi q}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hirr
  have hM_eq : M = Ideal.comap (Polynomial.mapRingHom pi)
    (Ideal.span {Polynomial.map pi q}) := by
    show Ideal.span {q} ⊔ Ideal.map Polynomial.C pp =
      Ideal.comap (Polynomial.mapRingHom pi) (Ideal.span {Polynomial.map pi q})
    rw [show Ideal.span {Polynomial.map pi q} =
      Ideal.map (Polynomial.mapRingHom pi) (Ideal.span {q}) by
      rw [Ideal.map_span, Set.image_singleton]; simp [Polynomial.coe_mapRingHom]]
    rw [Ideal.comap_map_of_surjective _
      (Polynomial.map_surjective pi Ideal.Quotient.mk_surjective)]
    congr 1
    rw [← RingHom.ker_eq_comap_bot, Polynomial.ker_mapRingHom, mk_ker]
  haveI : M.IsMaximal := by
    rw [hM_eq]
    exact Ideal.comap_isMaximal_of_surjective _
      (Polynomial.map_surjective pi Ideal.Quotient.mk_surjective)
  have hg_in_M : g ∈ M := by
    rw [hM_eq, Ideal.mem_comap]
    show (Polynomial.mapRingHom pi) g ∈ Ideal.span {Polynomial.map pi q}
    rwa [Ideal.mem_span_singleton]
  have hker_le : RingHom.ker (AdjoinRoot.mk g) ≤ M := by
    show RingHom.ker (Ideal.Quotient.mk (Ideal.span {g})) ≤ M
    rw [Ideal.mk_ker, Ideal.span_le]
    exact Set.singleton_subset_iff.mpr hg_in_M
  have hmmax : (Ideal.map (AdjoinRoot.mk g) M).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le AdjoinRoot.mk_surjective hker_le
  convert hmmax using 1
  show Ideal.map (algebraMap A (AdjoinRoot g)) pp ⊔ Ideal.span {AdjoinRoot.mk g q} =
    Ideal.map (AdjoinRoot.mk g) (Ideal.span {q} ⊔ Ideal.map Polynomial.C pp)
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton, Ideal.map_map, sup_comm]
  congr 1

/--
[AdjoinRoot.maximal_ideal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma AdjoinRoot.maximal_ideal_iff
  [CommRing A]
  [IsLocalRing A]
  [IsNoetherianRing A]
  {g : Polynomial A}
  [hA : Module.Finite A (AdjoinRoot g)]
  {𝔪 : Ideal (AdjoinRoot g)} :
-- imply
  𝔪.IsMaximal ↔ ∃ (q : Polynomial A), Irreducible (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧ (q.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∣ (g.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A))) ∧ 𝔪 = Ideal.map (algebraMap A (AdjoinRoot g)) (IsLocalRing.maximalIdeal A) ⊔ Ideal.span {AdjoinRoot.mk g q} := by
-- proof
  constructor
  · intro h𝔪
    haveI := h𝔪
    exact AdjoinRoot.maximal_ideal_form g 𝔪
  · rintro ⟨q, hirr, hdvd, rfl⟩
    exact AdjoinRoot.is_maximal_of_irreducible_factor g q hirr hdvd

/--
[subalgebra_eq_top_of_mod_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma subalgebra_eq_top_of_mod_maximal
  [CommRing A]
  [IsLocalRing A]
  [CommRing B]
  [Algebra A B]
  [Module.Finite A B]
  {S : Subalgebra A B}
-- given
  (h : (⊤ : Submodule A B) ≤ S.toSubmodule ⊔ (IsLocalRing.maximalIdeal A) • ⊤) :
-- imply
  S = ⊤ := by
-- proof
  have hle := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top ?_ h
  · rw [eq_top_iff]
    intro b _
    exact hle Submodule.mem_top
  · rw [IsLocalRing.jacobson_eq_maximalIdeal]
    exact bot_ne_top

/--
[isDVRUnramified_isSeparable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma isDVRUnramified_isSeparable
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
-- given
  (hunr : IsDVRUnramified A B) :
-- imply
  Algebra.IsSeparable K L := by
-- proof
  have hmap : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) =
    IsLocalRing.maximalIdeal B := by
    set I := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)
    have hle : I ≤ IsLocalRing.maximalIdeal B := by
      rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
    have hnotleq : ¬(I ≤ IsLocalRing.maximalIdeal B ^ 2) := by
      rw [← Ideal.ramificationIdx_ne_one_iff hle]
      simp [hunr.ramIdx_eq_one]
    have hIne : I ≠ ⊥ := fun h => hnotleq (h ▸ bot_le)
    obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B
      (IsPrincipalIdealRing.principal _) I hIne
    rw [hn] at hle hnotleq ⊢
    have h1 : n ≥ 1 := by
      by_contra h
      push Not at h
      interval_cases n
      simp at hle
      exact (IsLocalRing.maximalIdeal.isMaximal (R := B)).ne_top
        (eq_top_iff.mpr (by simpa using hle))
    have h2 : ¬(n ≥ 2) := fun h => hnotleq (Ideal.pow_le_pow_right h)
    have : n = 1 := by omega
    rw [this, pow_one]
  haveI : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    hunr.residue_separable
  haveI : Algebra.FormallyUnramified A B := Algebra.FormallyUnramified.of_map_maximalIdeal hmap
  haveI : Algebra.FormallyUnramified B L :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors B)
  haveI : Algebra.FormallyUnramified A L := Algebra.FormallyUnramified.comp A B L
  haveI : Algebra.FormallyUnramified K L :=
    Algebra.FormallyUnramified.localization_base (nonZeroDivisors A)
  exact Algebra.FormallyUnramified.isSeparable K L

/--
[isDVRUnramified_implies_formallyUnramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma isDVRUnramified_implies_formallyUnramified
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
-- given
  (hunr : IsDVRUnramified A B) :
-- imply
  Algebra.FormallyUnramified K L := by
-- proof
  have hsep := isDVRUnramified_isSeparable A K B L hunr
  exact Algebra.FormallyUnramified.of_isSeparable K L
set_option maxHeartbeats 1600000 in

/--
[cyclotomic_dvr_unramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma cyclotomic_dvr_unramified
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [Fintype (IsLocalRing.ResidueField A)]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  {m : ℕ}
  {ζ : L}
-- given
  (hm : Nat.Coprime m (ringChar (IsLocalRing.ResidueField A)))
  (hζ : IsPrimitiveRoot ζ m)
  (hgen : IntermediateField.adjoin K ({ζ} : Set L) = ⊤) :
-- imply
  IsDVRUnramified A B := by
-- proof
  set k := IsLocalRing.ResidueField A
  set l := IsLocalRing.ResidueField B
  have hsep : Algebra.IsSeparable k l := by
    haveI : Module.Finite k l := IsLocalRing.ResidueField.finite_of_module_finite
    haveI : Finite k := inferInstance
    haveI : PerfectField k := PerfectField.ofFinite
    haveI : Algebra.IsAlgebraic k l := Algebra.IsAlgebraic.of_finite k l
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hram : (IsLocalRing.maximalIdeal A).ramificationIdx
    (IsLocalRing.maximalIdeal B) = 1 := by
    have hm_pos : 0 < m := by
      obtain _ | n := m
      · exfalso; simp [Nat.Coprime] at hm; exact not_subsingleton k hm
      · exact Nat.succ_pos n
    have hinj_AB : Function.Injective (algebraMap A B) := by
      have : Function.Injective (algebraMap A L) := by
        rw [IsScalarTower.algebraMap_eq A K L]
        exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
      rw [IsScalarTower.algebraMap_eq A B L] at this
      exact Function.Injective.of_comp this
    haveI : NoZeroSMulDivisors A B := by
      constructor; intro a b hab
      simp only [Algebra.smul_def] at hab
      obtain h | h := mul_eq_zero.mp hab
      · left; exact hinj_AB (by rwa [map_zero])
      · right; exact h
    haveI : IsIntegrallyClosed B := GCDMonoid.toIsIntegrallyClosed
    have hζ_intB : IsIntegral B ζ := by
      refine ⟨X ^ m - C 1, ?_, ?_⟩
      · exact (monic_X_pow m).sub_of_left (by simp [degree_one, hm_pos])
      · simp [eval₂_sub, eval₂_pow, eval₂_X, hζ.pow_eq_one]
    rw [IsIntegrallyClosed.isIntegral_iff] at hζ_intB
    obtain ⟨ζ_B, hζ_eq⟩ := hζ_intB
    have hζ_pow : ζ_B ^ m = 1 := by
      apply IsFractionRing.injective B L
      simp [hζ_eq, hζ.pow_eq_one]
    have hζ_intA : IsIntegral A ζ_B := by
      refine ⟨X ^ m - C 1, ?_, ?_⟩
      · exact (monic_X_pow m).sub_of_left (by simp [degree_one, hm_pos])
      · simp [eval₂_sub, eval₂_pow, eval₂_X, hζ_pow]
    haveI : IsIntegrallyClosed A := GCDMonoid.toIsIntegrallyClosed
    set gA := minpoly A ζ_B
    set gbar := gA.map (IsLocalRing.residue A)
    have hmon : gA.Monic := minpoly.monic hζ_intA
    have hirr_gA : Irreducible gA := minpoly.irreducible hζ_intA
    have hdvd : gA ∣ X ^ m - C 1 :=
      minpoly.isIntegrallyClosed_dvd hζ_intA (by simp [hζ_pow])
    have hm_ne : (m : k) ≠ 0 := by
      intro h
      have hd : ringChar k ∣ m := ringChar.dvd h
      have h1 : ringChar k ∣ 1 := by rw [← hm]; exact Nat.dvd_gcd hd dvd_rfl
      have h2 : ringChar k ≤ 1 := Nat.le_of_dvd one_pos h1
      obtain h0 | h1r := show ringChar k = 0 ∨ ringChar k = 1 by omega
      · rw [h0] at hd; simp at hd; rw [hd] at hm; simp [Nat.Coprime] at hm
        exact not_subsingleton k hm
      · have : (1 : k) = 0 := by
        have hc := @CharP.cast_eq_zero k _ (ringChar k) (ringChar.charP k)
        rw [h1r] at hc; simp at hc
        exact one_ne_zero this
    have hdvd_bar : gbar ∣ X ^ m - C 1 := by
      have h1 := Polynomial.map_dvd (IsLocalRing.residue A) hdvd
      rwa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
        Polynomial.map_C, map_one] at h1
    have hsep_xm : (X ^ m - C (1 : k)).Separable :=
      separable_X_pow_sub_C 1 hm_ne one_ne_zero
    have hsep_gbar : gbar.Separable := hsep_xm.of_dvd hdvd_bar
    have hmon_gbar : gbar.Monic := hmon.map _
    have hdeg_pos : 0 < gbar.natDegree := by
      rw [hmon.natDegree_map]; exact minpoly.natDegree_pos hζ_intA
    have hirred_gbar : Irreducible gbar := by
      constructor
      · intro hu; exact absurd (natDegree_eq_zero_of_isUnit hu) (by omega)
      · intro p q hpq
        have hcop : IsCoprime p q := (hpq ▸ hsep_gbar).isCoprime
        exact irreducible_no_coprime_factor_mod hirr_gA p q hpq hcop
    have hminpoly_eq : minpoly K ζ = gA.map (algebraMap A K) := by
      have h := minpoly.isIntegrallyClosed_eq_field_fractions K L hζ_intA
      rwa [hζ_eq] at h
    have hLK_deg : Module.finrank K L = gA.natDegree := by
      have hintK : IsIntegral K ζ := IsIntegral.of_finite K ζ
      have h1 := IntermediateField.adjoin.finrank hintK
      rw [hgen] at h1
      rw [IntermediateField.finrank_top'] at h1
      rw [h1, hminpoly_eq, hmon.natDegree_map]
    set ζbar := IsLocalRing.residue B ζ_B
    have heval_gbar : Polynomial.aeval ζbar gbar = 0 := by
      show Polynomial.aeval ζbar (gA.map (IsLocalRing.residue A)) = 0
      simp only [Polynomial.aeval_def, Polynomial.eval₂_map]
      have hcomp : (algebraMap k l).comp (IsLocalRing.residue A) =
        (IsLocalRing.residue B).comp (algebraMap A B) := by ext; rfl
      rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
    have hintk : IsIntegral k ζbar := ⟨gbar, hmon_gbar, heval_gbar⟩
    have heq_minpoly_k : gbar = minpoly k ζbar :=
      minpoly.eq_of_irreducible_of_monic hirred_gbar heval_gbar hmon_gbar
    haveI : Module.Finite k l := IsLocalRing.ResidueField.finite_of_module_finite
    haveI : Module.Free k l := Module.Free.of_divisionRing k l
    have hdeg_le : (minpoly k ζbar).natDegree ≤ Module.finrank k l :=
      minpoly.natDegree_le ζbar
    have hfl_ge : Module.finrank k l ≥ Module.finrank K L := by
      calc Module.finrank k l ≥ (minpoly k ζbar).natDegree := hdeg_le
        _ = gbar.natDegree := by rw [← heq_minpoly_k]
        _ = gA.natDegree := hmon.natDegree_map _
        _ = Module.finrank K L := hLK_deg.symm
    set 𝔭 := IsLocalRing.maximalIdeal A
    set 𝔮 := IsLocalRing.maximalIdeal B
    haveI : 𝔮.LiesOver 𝔭 :=
      IsLocalRing.ResidueField.instLiesOverMaximalIdeal
    have efn : 𝔭.ramificationIdx 𝔮 * 𝔭.inertiaDeg 𝔮 = Module.finrank K L :=
      ramificationIdx_mul_inertiaDeg_of_isLocalRing B K L
        (IsDiscreteValuationRing.not_a_field A)
    have f_eq : 𝔭.inertiaDeg 𝔮 = Module.finrank k l :=
      inertiaDeg_algebraMap 𝔭 𝔮
    set e := 𝔭.ramificationIdx 𝔮
    have h_emul : e * Module.finrank k l = Module.finrank K L := by
      rw [← f_eq]; exact efn
    have hn_pos : 0 < Module.finrank K L := Module.finrank_pos
    have hf_pos : 0 < Module.finrank k l := by omega
    have he_le : e ≤ 1 := by
      by_contra h
      push Not at h
      have h2 : 2 ≤ e := h
      have : 2 * Module.finrank k l ≤ e * Module.finrank k l :=
        Nat.mul_le_mul_right _ h2
      omega
    have he_pos : 0 < e := by
      by_contra h
      push Not at h
      interval_cases e
      simp at h_emul; omega
    omega
  exact ⟨hram, hsep⟩
section Theorem_10_12
variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]

/--
[mod_maximal_surjection_general](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma mod_maximal_surjection_general
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {ᾱ : IsLocalRing.ResidueField B}
  {α : B}
  {b : B}
-- given
  (hᾱ : IntermediateField.adjoin (IsLocalRing.ResidueField A) {ᾱ} = ⊤)
  (hα : (IsLocalRing.residue B) α = ᾱ) :
-- imply
  ∃ s ∈ (Algebra.adjoin A ({α} : Set B)).toSubmodule, b - s ∈ IsLocalRing.maximalIdeal B := by
-- proof
  have hadj_k : Algebra.adjoin (IsLocalRing.ResidueField A)
    ({ᾱ} : Set (IsLocalRing.ResidueField B)) = ⊤ := by
    have hint := IsIntegral.of_finite (IsLocalRing.ResidueField A) ᾱ
    have h := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic
    rw [hᾱ, IntermediateField.top_toSubalgebra] at h; exact h.symm
  have hadj_A : Algebra.adjoin A ({ᾱ} : Set (IsLocalRing.ResidueField B)) = ⊤ := by
    have key0 := Algebra.Subalgebra.restrictScalars_adjoin A
      (S := IsLocalRing.ResidueField A) (A := IsLocalRing.ResidueField B)
      (s := ({ᾱ} : Set (IsLocalRing.ResidueField B)))
    rw [hadj_k] at key0
    have htop : Subalgebra.restrictScalars A
      (⊤ : Subalgebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) = ⊤ := by
      ext; simp
    rw [htop] at key0
    have hrange_le : (IsScalarTower.toAlgHom A
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).range ≤
      Algebra.adjoin A ({ᾱ} : Set (IsLocalRing.ResidueField B)) := by
      rintro x ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) y
      show algebraMap A (IsLocalRing.ResidueField B) a ∈ _
      exact Subalgebra.algebraMap_mem _ _
    rwa [sup_eq_right.mpr hrange_le] at key0
  set φ : B →ₐ[A] IsLocalRing.ResidueField B :=
    Ideal.Quotient.mkₐ A (IsLocalRing.maximalIdeal B)
  have hφα : φ α = ᾱ := hα
  have himage : Subalgebra.map φ (Algebra.adjoin A ({α} : Set B)) = ⊤ := by
    rw [AlgHom.map_adjoin_singleton, hφα, hadj_A]
  have hb_im : φ b ∈ Subalgebra.map φ (Algebra.adjoin A ({α} : Set B)) := by
    rw [himage]; trivial
  obtain ⟨s, hs, hφs⟩ := hb_im
  exact ⟨s, hs, by rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]; exact hφs.symm⟩

/--
[unit_mul_irreducible_not_sq'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma unit_mul_irreducible_not_sq'
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {u : B}
  {p : B}
-- given
  (hu : IsUnit u)
  (hp : Irreducible p) :
-- imply
  u * p ∉ IsLocalRing.maximalIdeal B ^ 2 := by
-- proof
  rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro ⟨c, hc⟩
  have h1 : u = c * p :=
    mul_left_cancel₀ hp.ne_zero (show p * u = p * (c * p) by rw [mul_comm p u, hc]; ring)
  have h2 : u ∈ IsLocalRing.maximalIdeal B := by
    rw [hp.maximalIdeal_eq, Ideal.mem_span_singleton]; exact ⟨c, by rw [h1, mul_comm]⟩
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h2; exact h2 hu

/--
[irreducible_of_mem_not_sq'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma irreducible_of_mem_not_sq'
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {x : B}
-- given
  (hx_in : x ∈ IsLocalRing.maximalIdeal B)
  (hx_not : x ∉ IsLocalRing.maximalIdeal B ^ 2) :
-- imply
  Irreducible x := by
-- proof
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_prime (R := B)
  rw [hp.irreducible.maximalIdeal_eq] at hx_in hx_not
  rw [Ideal.mem_span_singleton] at hx_in; obtain ⟨u, hu⟩ := hx_in
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hx_not
  have hIsUnit : IsUnit u := by
    by_contra h; apply hx_not; rw [hu]
    have : u ∈ IsLocalRing.maximalIdeal B := by rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [hp.irreducible.maximalIdeal_eq, Ideal.mem_span_singleton] at this
    obtain ⟨v, hv⟩ := this; exact ⟨v, by rw [hv]; ring⟩
  have hassoc : Associated p x := ⟨hIsUnit.unit, by rw [hu]; simp [IsUnit.unit_spec]⟩
  exact Associated.irreducible hassoc hp.irreducible
omit [Module.Finite A B] in
set_option maxHeartbeats 1600000 in

/--
[uniformizer_in_adjoin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma uniformizer_in_adjoin
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {abar : IsLocalRing.ResidueField B}
  {α₀ : B}
-- given
  (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
  (_habar : IntermediateField.adjoin (IsLocalRing.ResidueField A) {abar} = ⊤)
  (hα₀ : (IsLocalRing.residue B) α₀ = abar) :
-- imply
  ∃ α : B, (IsLocalRing.residue B) α = abar ∧ ∃ π ∈ (Algebra.adjoin A ({α} : Set B)).toSubmodule, Irreducible π := by
-- proof
  let k := IsLocalRing.ResidueField A
  let l := IsLocalRing.ResidueField B
  have hg_sep : (minpoly k abar).Separable := Algebra.IsSeparable.isSeparable k abar
  obtain ⟨G, hG⟩ := Polynomial.map_surjective (IsLocalRing.residue A)
    (fun x => IsLocalRing.residue_surjective x) (minpoly k abar)
  have residue_aeval : ∀ (p : Polynomial A) (b : B),
    (IsLocalRing.residue B) (Polynomial.aeval b p) =
    Polynomial.aeval ((IsLocalRing.residue B) b) (Polynomial.map (IsLocalRing.residue A) p) := by
    intro p b; simp only [Polynomial.aeval_def]
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_map]; congr 1
  have hGα₀_mem : Polynomial.aeval α₀ G ∈ IsLocalRing.maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; intro hunit
    have : (IsLocalRing.residue B) (Polynomial.aeval α₀ G) ≠ 0 :=
      IsUnit.ne_zero (hunit.map (IsLocalRing.residue B))
    rw [residue_aeval, hG, hα₀, minpoly.aeval] at this; exact this rfl
  have hGα₀_deriv_unit : IsUnit (Polynomial.aeval α₀ (Polynomial.derivative G)) := by
    by_contra hmem; rw [← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal] at hmem
    have hzero : (IsLocalRing.residue B) (Polynomial.aeval α₀ (Polynomial.derivative G)) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [residue_aeval] at hzero
    rw [show Polynomial.map (IsLocalRing.residue A) (Polynomial.derivative G) =
      Polynomial.derivative (Polynomial.map (IsLocalRing.residue A) G) from
      (Polynomial.derivative_map G (IsLocalRing.residue A)).symm] at hzero
    rw [hG, hα₀] at hzero
    exact Polynomial.Separable.aeval_derivative_ne_zero hg_sep (minpoly.aeval k abar) hzero
  by_cases hcase : Polynomial.aeval α₀ G ∈ IsLocalRing.maximalIdeal B ^ 2
  ·
    obtain ⟨p₀, hp₀⟩ := IsDiscreteValuationRing.exists_prime (R := B)
    use α₀ + p₀
    constructor
    · simp only [map_add, hα₀]
      have : (IsLocalRing.residue B) p₀ = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr
          (hp₀.irreducible.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self p₀)
      simp [this]
    · set GB := Polynomial.map (algebraMap A B) G
      obtain ⟨κ, hκ⟩ := Polynomial.binomExpansion GB α₀ p₀
      have heval_eq : GB.eval α₀ = Polynomial.aeval α₀ G := by
        simp [GB, Polynomial.eval_map, Polynomial.aeval_def]
      have heval_add : GB.eval (α₀ + p₀) = Polynomial.aeval (α₀ + p₀) G := by
        simp [GB, Polynomial.eval_map, Polynomial.aeval_def]
      have hderiv_eq : (Polynomial.derivative GB).eval α₀ =
        Polynomial.aeval α₀ (Polynomial.derivative G) := by
        simp [GB, Polynomial.derivative_map, Polynomial.eval_map, Polynomial.aeval_def]
      have hexp : Polynomial.aeval (α₀ + p₀) G =
        Polynomial.aeval α₀ G + Polynomial.aeval α₀ (Polynomial.derivative G) * p₀ + κ * p₀ ^ 2 := by
        rw [← heval_add, ← heval_eq, ← hderiv_eq]; exact hκ
      have hmem_m : Polynomial.aeval (α₀ + p₀) G ∈ IsLocalRing.maximalIdeal B := by
        rw [hexp]
        have h1 : Polynomial.aeval α₀ G ∈ IsLocalRing.maximalIdeal B := hGα₀_mem
        have h2 : Polynomial.aeval α₀ (Polynomial.derivative G) * p₀ ∈ IsLocalRing.maximalIdeal B := by
          rw [mul_comm]
          exact Ideal.mul_mem_right _ _ (hp₀.irreducible.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self p₀)
        have h3 : κ * p₀ ^ 2 ∈ IsLocalRing.maximalIdeal B := by
          apply Ideal.mul_mem_left
          rw [sq]; apply Ideal.mul_mem_left
          exact hp₀.irreducible.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self p₀
        exact (IsLocalRing.maximalIdeal B).add_mem ((IsLocalRing.maximalIdeal B).add_mem h1 h2) h3
      have hnot_sq : Polynomial.aeval (α₀ + p₀) G ∉ IsLocalRing.maximalIdeal B ^ 2 := by
        intro hmem2
        have hderp : Polynomial.aeval α₀ (Polynomial.derivative G) * p₀ ∈ IsLocalRing.maximalIdeal B ^ 2 := by
          have heq : Polynomial.aeval α₀ (Polynomial.derivative G) * p₀ =
            Polynomial.aeval (α₀ + p₀) G - Polynomial.aeval α₀ G - κ * p₀ ^ 2 := by
            calc Polynomial.aeval α₀ (Polynomial.derivative G) * p₀
              = (Polynomial.aeval α₀ G + Polynomial.aeval α₀ (Polynomial.derivative G) * p₀ + κ * p₀ ^ 2)
                - Polynomial.aeval α₀ G - κ * p₀ ^ 2 := by ring
              _ = Polynomial.aeval (α₀ + p₀) G - Polynomial.aeval α₀ G - κ * p₀ ^ 2 := by rw [← hexp]
          rw [heq]
          have h3 : κ * p₀ ^ 2 ∈ IsLocalRing.maximalIdeal B ^ 2 := by
            apply Ideal.mul_mem_left
            exact Ideal.pow_mem_pow (hp₀.irreducible.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self p₀) 2
          exact (IsLocalRing.maximalIdeal B ^ 2).sub_mem ((IsLocalRing.maximalIdeal B ^ 2).sub_mem hmem2 hcase) h3
        exact unit_mul_irreducible_not_sq' B _ hGα₀_deriv_unit _ hp₀.irreducible hderp
      refine ⟨Polynomial.aeval (α₀ + p₀) G, ?_, irreducible_of_mem_not_sq' B _ hmem_m hnot_sq⟩
      exact Polynomial.aeval_mem_adjoin_singleton A (α₀ + p₀)
  ·
    use α₀, hα₀
    refine ⟨Polynomial.aeval α₀ G, ?_, irreducible_of_mem_not_sq' B _ hGα₀_mem hcase⟩
    exact Polynomial.aeval_mem_adjoin_singleton A α₀

/--
[bootstrap_subalgebra_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma bootstrap_subalgebra_pow
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {S : Subalgebra A B}
  {π : B}
  {n : ℕ}
  {b : B}
-- given
  (hπ_irr : Irreducible π)
  (hπ_in : π ∈ S.toSubmodule)
  (hmod1 : ∀ b : B, ∃ s ∈ S.toSubmodule, b - s ∈ IsLocalRing.maximalIdeal B) :
-- imply
  ∃ s ∈ S.toSubmodule, b - s ∈ IsLocalRing.maximalIdeal B ^ n := by
-- proof
  induction n with
  | zero =>
    exact ⟨0, S.toSubmodule.zero_mem, by simp [pow_zero]⟩
  | succ n ih =>
    obtain ⟨s₀, hs₀, hbs₀⟩ := ih
    rw [hπ_irr.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hbs₀
    obtain ⟨c, hc⟩ := hbs₀
    obtain ⟨s₁, hs₁, hcs₁⟩ := hmod1 c
    rw [hπ_irr.maximalIdeal_eq, Ideal.mem_span_singleton] at hcs₁
    obtain ⟨d, hd⟩ := hcs₁
    have hπn_in : π ^ n ∈ S.toSubmodule := by
      rw [Subalgebra.mem_toSubmodule] at hπ_in ⊢; exact S.pow_mem hπ_in n
    have hπns₁_in : π ^ n * s₁ ∈ S.toSubmodule := by
      rw [Subalgebra.mem_toSubmodule] at hs₁ hπn_in ⊢
      exact S.mul_mem hπn_in hs₁
    refine ⟨s₀ + π ^ n * s₁, S.toSubmodule.add_mem hs₀ hπns₁_in, ?_⟩
    rw [hπ_irr.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    refine ⟨d, ?_⟩
    linear_combination hc + π ^ n * hd
omit [IsLocalHom (algebraMap A B)] in
set_option maxHeartbeats 800000 in

/--
[exists_maximal_pow_le_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma exists_maximal_pow_le_map
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A] :
-- imply
  ∃ e : ℕ, IsLocalRing.maximalIdeal B ^ e ≤ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) := by
-- proof
  have hne : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≠ ⊥ := by
    intro h
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_prime (R := A)
    have hp_mem : algebraMap A B p ∈ Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) :=
      Ideal.mem_map_of_mem _ (hp.irreducible.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self p)
    rw [h] at hp_mem
    simp only [Ideal.mem_bot] at hp_mem
    have hker_le : IsLocalRing.maximalIdeal A ≤ RingHom.ker (algebraMap A B) := by
      rw [hp.irreducible.maximalIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
      exact RingHom.mem_ker.mpr hp_mem
    have hφ : ∀ a ∈ IsLocalRing.maximalIdeal A, algebraMap A B a = 0 :=
      fun a ha => RingHom.mem_ker.mp (hker_le ha)
    letI : Algebra (A ⧸ IsLocalRing.maximalIdeal A) B :=
      (Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A B) hφ).toAlgebra
    set k := A ⧸ IsLocalRing.maximalIdeal A
    set f := Ideal.Quotient.lift (IsLocalRing.maximalIdeal A) (algebraMap A B) hφ
    have hfin : Module.Finite k B := by
      obtain ⟨s, hs⟩ := (Module.finite_def.mp ‹Module.Finite A B›)
      refine ⟨⟨s, ?_⟩⟩
      rw [eq_top_iff]; intro b _
      have hb : b ∈ Submodule.span A (s : Set B) := by rw [hs]; trivial
      refine Submodule.span_induction
        (p := fun x _ => x ∈ Submodule.span k (s : Set B))
        (fun x hx => Submodule.subset_span hx)
        (Submodule.zero_mem _)
        (fun x y _ _ hx hy => Submodule.add_mem _ hx hy)
        (fun r x _ hx => ?_)
        hb
      show r • x ∈ Submodule.span k (s : Set B)
      rw [Algebra.smul_def r x]
      have hlift : f (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) r) = algebraMap A B r :=
        Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal A) (algebraMap A B) hφ
      rw [← hlift]
      change (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A) r) • x ∈ _
      exact Submodule.smul_mem _ _ hx
    have hfield : IsField B := by
      have : Algebra.IsIntegral k B := by
        constructor; intro x; exact IsIntegral.of_finite k x
      exact isField_of_isIntegral_of_isField'
        ((Ideal.Quotient.field (IsLocalRing.maximalIdeal A)).toIsField)
    exact IsDiscreteValuationRing.not_isField B hfield
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_prime (R := B)
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hπ.irreducible
  exact ⟨e, by rw [hπ.irreducible.maximalIdeal_eq, Ideal.span_singleton_pow, he]⟩

/--
[adjusted_lift_spans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma adjusted_lift_spans
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {ᾱ : IsLocalRing.ResidueField B}
  {α₀ : B}
-- given
  (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
  (hᾱ : IntermediateField.adjoin (IsLocalRing.ResidueField A) {ᾱ} = ⊤)
  (hα₀ : (IsLocalRing.residue B) α₀ = ᾱ) :
-- imply
  ∃ α : B, ∀ b : B, ∃ s ∈ (Algebra.adjoin A ({α} : Set B)).toSubmodule, b - s ∈ (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)).restrictScalars A := by
-- proof
  obtain ⟨α, hαres, π, hπ_in, hπ_irr⟩ := uniformizer_in_adjoin A B hsep ᾱ hᾱ α₀ hα₀
  use α
  intro b
  have hmod1 : ∀ c : B, ∃ s ∈ (Algebra.adjoin A ({α} : Set B)).toSubmodule,
    c - s ∈ IsLocalRing.maximalIdeal B :=
    mod_maximal_surjection_general A B ᾱ hᾱ α hαres
  obtain ⟨e, he⟩ := exists_maximal_pow_le_map A B
  obtain ⟨s, hs, hbs⟩ := bootstrap_subalgebra_pow A B _ π hπ_irr hπ_in hmod1 e b
  exact ⟨s, hs, he hbs⟩

/--
[exists_spanning_element](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma exists_spanning_element
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
-- given
  (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :
-- imply
  ∃ α : B, (⊤ : Submodule A B) ≤ (Algebra.adjoin A ({α} : Set B)).toSubmodule ⊔ (IsLocalRing.maximalIdeal A) • ⊤ := by
-- proof
  obtain ⟨ᾱ, hᾱ⟩ := Field.exists_primitive_element
    (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
  obtain ⟨α₀, hα₀⟩ := IsLocalRing.residue_surjective ᾱ
  obtain ⟨α, hα⟩ := adjusted_lift_spans A B hsep ᾱ hᾱ α₀ hα₀
  refine ⟨α, ?_⟩
  rw [Ideal.smul_top_eq_map]
  intro b _
  obtain ⟨s, hs, hbs⟩ := hα b
  exact Submodule.mem_sup.2 ⟨s, hs, b - s, hbs, by ring⟩

/--
[dvr_monogenicity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma dvr_monogenicity
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
-- given
  (hsep : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) :
-- imply
  ∃ α : B, Algebra.adjoin A ({α} : Set B) = ⊤ := by
-- proof
  obtain ⟨α, hα⟩ := exists_spanning_element A B hsep
  exact ⟨α, subalgebra_eq_top_of_mod_maximal _ hα⟩

/--
[map_maximalIdeal_eq_of_ramificationIdx_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma map_maximalIdeal_eq_of_ramificationIdx_one
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
-- given
  (hunram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) = 1) :
-- imply
  Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) = IsLocalRing.maximalIdeal B := by
-- proof
  set I := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)
  have hle : I ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  have hnotleq : ¬(I ≤ IsLocalRing.maximalIdeal B ^ 2) := by
    rwa [← Ideal.ramificationIdx_ne_one_iff hle, not_not]
  have hIne : I ≠ ⊥ := fun h => hnotleq (h ▸ bot_le)
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal _) I hIne
  rw [hn] at hle hnotleq ⊢
  have h1 : n ≥ 1 := by
    by_contra h
    push Not at h
    interval_cases n
    simp at hle
    exact (IsLocalRing.maximalIdeal.isMaximal (R := B)).ne_top
      (eq_top_iff.mpr (by simpa using hle))
  have h2 : ¬(n ≥ 2) := fun h => hnotleq (Ideal.pow_le_pow_right h)
  have : n = 1 := by omega
  rw [this, pow_one]
set_option maxHeartbeats 800000 in

/--
[dvr_monogenicity_unramified_forall](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma dvr_monogenicity_unramified_forall
  {A B : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
  {ᾱ : IsLocalRing.ResidueField B}
  {α₀ : B}
-- given
  (_hsep : Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B))
  (hunram : (IsLocalRing.maximalIdeal A).ramificationIdx (IsLocalRing.maximalIdeal B) = 1)
  (hgen : Algebra.adjoin (IsLocalRing.ResidueField A) ({ᾱ} : Set (IsLocalRing.ResidueField B)) = ⊤)
  (hlift : IsLocalRing.residue B α₀ = ᾱ) :
-- imply
  Algebra.adjoin A ({α₀} : Set B) = ⊤ := by
-- proof
  apply subalgebra_eq_top_of_mod_maximal
  rw [Ideal.smul_top_eq_map]
  intro b _
  have hmap := map_maximalIdeal_eq_of_ramificationIdx_one A B hunram
  set φ : B →ₐ[A] IsLocalRing.ResidueField B :=
    Ideal.Quotient.mkₐ A (IsLocalRing.maximalIdeal B)
  have hφα : φ α₀ = ᾱ := hlift
  have himage : Subalgebra.map φ (Algebra.adjoin A ({α₀} : Set B)) =
    Algebra.adjoin A ({ᾱ} : Set (IsLocalRing.ResidueField B)) := by
    rw [AlgHom.map_adjoin_singleton, hφα]
  have hadj_top : Algebra.adjoin A ({ᾱ} : Set (IsLocalRing.ResidueField B)) = ⊤ := by
    have key0 := Algebra.Subalgebra.restrictScalars_adjoin A
      (S := IsLocalRing.ResidueField A) (A := IsLocalRing.ResidueField B)
      (s := ({ᾱ} : Set (IsLocalRing.ResidueField B)))
    rw [hgen] at key0
    have htop : Subalgebra.restrictScalars A
      (⊤ : Subalgebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)) = ⊤ := by
      ext; simp
    rw [htop] at key0
    have hrange_le : (IsScalarTower.toAlgHom A
      (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)).range ≤
      Algebra.adjoin A ({ᾱ} : Set (IsLocalRing.ResidueField B)) := by
      rintro x ⟨y, rfl⟩
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective (R := A) y
      show algebraMap A (IsLocalRing.ResidueField B) a ∈ _
      exact Subalgebra.algebraMap_mem _ _
    rwa [sup_eq_right.mpr hrange_le] at key0
  rw [hadj_top] at himage
  have hb_in_image : φ b ∈ Subalgebra.map φ (Algebra.adjoin A ({α₀} : Set B)) := by
    rw [himage]; trivial
  obtain ⟨s, hs, hφs⟩ := hb_in_image
  have hmem : b - s ∈ IsLocalRing.maximalIdeal B := by
    rwa [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  rw [← hmap] at hmem
  exact Submodule.mem_sup.mpr ⟨s, hs, b - s, hmem, by ring⟩
end Theorem_10_12
section Def_10_21
variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/--
[isFiniteUnramifiedSubext_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma isFiniteUnramifiedSubext_map
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {E : IntermediateField K L}
  {σ : L ≃ₐ[K] L}
-- given
  (hE : IsFiniteUnramifiedSubext A K L E) :
-- imply
  IsFiniteUnramifiedSubext A K L (E.map (σ : L →ₐ[K] L)) := by
-- proof
  obtain ⟨hfin, hunr⟩ := hE
  constructor
  · exact LinearEquiv.finiteDimensional
    (IntermediateField.intermediateFieldMap σ E).toLinearEquiv
  ·
    let e : ↥E ≃ₐ[A] ↥(E.map (σ : L →ₐ[K] L)) :=
      (IntermediateField.intermediateFieldMap σ E).restrictScalars A
    exact Algebra.FormallyUnramified.of_equiv (e.mapIntegralClosure)

/--
[maximalUnramifiedSubextension_map_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma maximalUnramifiedSubextension_map_le
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {σ : L ≃ₐ[K] L} :
-- imply
  (maximalUnramifiedSubextension A K L).map (σ : L →ₐ[K] L) ≤ maximalUnramifiedSubextension A K L := by
-- proof
  simp only [maximalUnramifiedSubextension]
  rw [IntermediateField.map_iSup]
  apply iSup_le; intro E
  rw [IntermediateField.map_iSup]
  apply iSup_le; intro hE
  apply le_iSup_of_le (E.map (σ : L →ₐ[K] L))
  apply le_iSup_of_le (isFiniteUnramifiedSubext_map A K L E hE σ)
  exact le_refl _

/--
[maximalUnramifiedSubextension_map_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma maximalUnramifiedSubextension_map_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L]
  {σ : L ≃ₐ[K] L} :
-- imply
  (maximalUnramifiedSubextension A K L).map (σ : L →ₐ[K] L) = maximalUnramifiedSubextension A K L := by
-- proof
  apply le_antisymm
  · exact maximalUnramifiedSubextension_map_le A K L σ
  · intro x hx
    rw [IntermediateField.mem_map]
    have hx' : σ.symm x ∈ maximalUnramifiedSubextension A K L := by
      apply maximalUnramifiedSubextension_map_le A K L σ.symm
      rw [IntermediateField.mem_map]
      exact ⟨x, hx, by simp⟩
    exact ⟨σ.symm x, hx', by simp⟩

/--
[coprime_pred_of_prime_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma coprime_pred_of_prime_dvd
  {p m : ℕ}
-- given
  (hp : Nat.Prime p)
  (hm : 1 ≤ m)
  (hdvd : p ∣ m) :
-- imply
  Nat.Coprime (m - 1) p := by
-- proof
  rw [Nat.coprime_comm]
  exact (hp.coprime_iff_not_dvd).mpr (fun h => by
    have h1 : p ∣ m - (m - 1) := Nat.dvd_sub hdvd h
    rw [Nat.sub_sub_self hm] at h1
    exact absurd (Nat.le_of_dvd Nat.one_pos h1) (not_le.mpr hp.one_lt))

/--
[finite_field_coprime_pred_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma finite_field_coprime_pred_pow
  {F : Type*}
  [Field F]
  [Fintype F]
  {n : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  Nat.Coprime (Fintype.card F ^ n - 1) (ringChar F) := by
-- proof
  apply coprime_pred_of_prime_dvd
  · obtain ⟨_, hp, _⟩ := FiniteField.card (K := F) (p := ringChar F); exact hp
  · exact Nat.one_le_pow n _ Fintype.card_pos
  · obtain ⟨m, _, hcard⟩ := FiniteField.card (K := F) (p := ringChar F)
    rw [hcard]; exact dvd_pow (dvd_pow_self _ (PNat.ne_zero m)) (by omega)
section Cor_10_17

/--
[henselian_prim_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma henselian_prim_root
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsLocalRing A]
  [HenselianLocalRing A]
  [Fintype (IsLocalRing.ResidueField A)] :
-- imply
  ∃ ζ : A, IsPrimitiveRoot ζ (Fintype.card (IsLocalRing.ResidueField A) - 1) := by
-- proof
  classical
  obtain ⟨g, hg_order⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (IsLocalRing.ResidueField A)ˣ)
  have hprim_units : IsPrimitiveRoot g (Fintype.card (IsLocalRing.ResidueField A) - 1) := by
    have h := IsPrimitiveRoot.orderOf g
    rwa [hg_order, Nat.card_eq_fintype_card, Fintype.card_units] at h
  have hprim_val : IsPrimitiveRoot (g : IsLocalRing.ResidueField A)
    (Fintype.card (IsLocalRing.ResidueField A) - 1) :=
    hprim_units.map_of_injective (f := Units.coeHom _) (fun a b h => Units.ext h)
  set n := Fintype.card (IsLocalRing.ResidueField A) - 1
  by_cases hn : n = 0
  · rw [hn]; exact ⟨0, IsPrimitiveRoot.zero⟩
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hensel := ((HenselianLocalRing.TFAE (R := A)).out 0 1).mp ‹HenselianLocalRing A›
    set f : A[X] := X ^ n - C 1
    have hf_monic : f.Monic := by
      apply (monic_X_pow n).sub_of_left
      calc degree (C (1 : A)) ≤ 0 := degree_C_le
        _ < ↑n := by exact_mod_cast hn_pos
        _ = degree (X ^ n : A[X]) := by rw [degree_X_pow]
    have heval_zero : aeval (g : IsLocalRing.ResidueField A) f = 0 := by
      simp only [f, map_sub, map_pow, aeval_X, map_one, hprim_val.pow_eq_one, sub_self]
    have hderiv_ne : aeval (g : IsLocalRing.ResidueField A) (Polynomial.derivative f) ≠ 0 := by
      simp only [f, derivative_sub, derivative_pow, derivative_X, mul_one, derivative_C, sub_zero]
      simp only [map_mul, map_natCast, aeval_X_pow]
      apply mul_ne_zero
      · rw [show (n : IsLocalRing.ResidueField A) =
        ↑(Fintype.card (IsLocalRing.ResidueField A) - 1) from rfl]
        rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card (IsLocalRing.ResidueField A)),
          Nat.cast_card_eq_zero (IsLocalRing.ResidueField A), zero_sub]
        simp
      · exact pow_ne_zero _ g.ne_zero
    obtain ⟨ζ, hζ_root, hζ_res⟩ :=
      hensel f hf_monic (g : IsLocalRing.ResidueField A) heval_zero hderiv_ne
    have hζ_pow : ζ ^ n = 1 := by
      simp only [f, IsRoot, eval_sub, eval_pow, eval_X, eval_C] at hζ_root
      exact sub_eq_zero.mp hζ_root
    exact ⟨ζ, hζ_pow, fun m hm => by
      have : (IsLocalRing.residue A ζ) ^ m = 1 := by rw [← map_pow, hm, map_one]
      rw [hζ_res] at this
      exact hprim_val.dvd_of_pow_eq_one m this⟩

/--
[algebraMap_integralClosure_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma algebraMap_integralClosure_injective
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [Algebra A L]
  [IsScalarTower A K L] :
-- imply
  Function.Injective (algebraMap A ↥(integralClosure A L)) := by
-- proof
  intro a b hab
  have : (algebraMap ↥(integralClosure A L) L) (algebraMap A ↥(integralClosure A L) a) =
    (algebraMap ↥(integralClosure A L) L) (algebraMap A ↥(integralClosure A L) b) := congr_arg _ hab
  simp only [← IsScalarTower.algebraMap_apply A ↥(integralClosure A L) L] at this
  have h2 : algebraMap K L (algebraMap A K a) = algebraMap K L (algebraMap A K b) := by
    rwa [← IsScalarTower.algebraMap_apply A K L, ← IsScalarTower.algebraMap_apply A K L]
  exact IsFractionRing.injective A K ((algebraMap K L).injective h2)

/--
[isPrecomplete_of_pow_localExt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma isPrecomplete_of_pow_localExt
  [CommRing R]
  {I : Ideal R}
  [AddCommGroup M]
  [Module R M]
  {e : ℕ}
  [hpc : IsPrecomplete (I ^ e) M]
-- given
  (he : 1 ≤ e) :
-- imply
  IsPrecomplete I M := by
-- proof
  constructor
  intro f hf
  have hcauchy : ∀ {m n : ℕ}, m ≤ n →
    f (m * e) ≡ f (n * e) [SMOD (I ^ e) ^ m • (⊤ : Submodule R M)] := by
    intro m n hmn
    rw [show (I ^ e) ^ m = I ^ (m * e) from by rw [← pow_mul, mul_comm]]
    exact hf (Nat.mul_le_mul_right e hmn)
  obtain ⟨L, hL⟩ := hpc.prec' (fun n => f (n * e)) hcauchy
  exact ⟨L, fun n => by
    have h1 : f n ≡ f (n * e) [SMOD I ^ n • (⊤ : Submodule R M)] :=
      hf (Nat.le_mul_of_pos_right n (by omega))
    have h2 : f (n * e) ≡ L [SMOD (I ^ e) ^ n • (⊤ : Submodule R M)] := hL n
    rw [show (I ^ e) ^ n = I ^ (n * e) from by rw [← pow_mul, mul_comm]] at h2
    exact h1.trans (SModEq.mono (Submodule.smul_mono_left
      (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right n (by omega)))) h2)⟩
set_option maxHeartbeats 800000 in

/--
[integral_closure_isAdicComplete](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma integral_closure_isAdicComplete
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable K L]
  [IsLocalRing ↥(integralClosure A L)] :
-- imply
  IsAdicComplete (IsLocalRing.maximalIdeal ↥(integralClosure A L)) ↥(integralClosure A L) := by
-- proof
  set B := ↥(integralClosure A L) with hB_def
  have hinj : Function.Injective (algebraMap A B) :=
    algebraMap_integralClosure_injective A K L
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  haveI : Algebra.IsIntegral A B := integralClosure.AlgebraIsIntegral
  haveI : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  haveI : Module.Finite A B := IsIntegralClosure.finite A K L (integralClosure A L)
  haveI : IsDedekindDomain B := IsIntegralClosure.isDedekindDomain A K L (integralClosure A L)
  haveI : IsPrincipalIdealRing B := IsDedekindDomain.isPrincipalIdealRing B
  haveI : IsDiscreteValuationRing B := {
    not_a_field' := by
      intro h
      exact IsDiscreteValuationRing.not_isField A
        (isField_of_isIntegral_of_isField hinj (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h))
  }
  rw [isAdicComplete_iff]
  refine ⟨inferInstance, ?_⟩
  have hpc_A : IsPrecomplete (IsLocalRing.maximalIdeal A) B := by
    rw [← AdicCompletion.of_surjective_iff]
    set I := IsLocalRing.maximalIdeal A
    have hsurj_tp := AdicCompletion.ofTensorProduct_surjective_of_finite I B
    have hsurj_A : Function.Surjective (AdicCompletion.of I A) :=
      (AdicCompletion.of_bijective_iff.mpr inferInstance).2
    suffices h : ∀ t, AdicCompletion.ofTensorProduct I B t ∈
      LinearMap.range (AdicCompletion.of I B) by
      intro y
      obtain ⟨t, ht⟩ := hsurj_tp y
      exact ⟨(h t).choose, by rw [(h t).choose_spec, ht]⟩
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r b =>
      obtain ⟨a, ha⟩ := hsurj_A r
      exact ⟨a • b, by
        rw [AdicCompletion.ofTensorProduct_tmul, ← ha, map_smul]; rfl⟩
    | add x y hx hy =>
      obtain ⟨bx, hbx⟩ := hx
      obtain ⟨by_, hby⟩ := hy
      exact ⟨bx + by_, by simp [map_add, hbx, hby]⟩
  have hpc_map : IsPrecomplete (Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A)) B :=
    IsPrecomplete.map_algebraMap_iff.mpr hpc_A
  set J := Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) with hJ_def
  have hle : J ≤ IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  have hJne : J ≠ ⊥ := by
    intro h
    rw [hJ_def, Ideal.map_eq_bot_iff_le_ker] at h
    have hker : RingHom.ker (algebraMap A B) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp hinj
    rw [hker] at h
    exact IsDiscreteValuationRing.not_a_field A (le_bot_iff.mp h)
  obtain ⟨e, he⟩ := exists_maximalIdeal_pow_eq_of_principal B
    (IsPrincipalIdealRing.principal _) J hJne
  have he1 : 1 ≤ e := by
    by_contra h
    push Not at h
    interval_cases e
    simp only [pow_zero, Ideal.one_eq_top] at he
    exact (IsLocalRing.maximalIdeal.isMaximal (R := B)).ne_top
      (eq_top_iff.mpr (he ▸ hle))
  rw [he] at hpc_map
  exact isPrecomplete_of_pow_localExt e he1 (hpc := hpc_map)

/--
[integral_closure_isHenselian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma integral_closure_isHenselian
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable K L] :
-- imply
  HenselianLocalRing ↥(integralClosure A L) := by
-- proof
  haveI : IsLocalRing ↥(integralClosure A L) := integral_closure_isLocalRing A K L
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(integralClosure A L))
    ↥(integralClosure A L) := integral_closure_isAdicComplete A K L
  exact {
    is_henselian := by
      intro f hf a₀ h₁ h₂
      have h₂' : IsUnit (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal ↥(integralClosure A L)) (f.derivative.eval a₀)) :=
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal ↥(integralClosure A L))).isUnit_map h₂
      exact HenselianRing.is_henselian f hf a₀ h₁ h₂'
  }

/--
[root_of_unity_eq_one_of_congr_mod_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma root_of_unity_eq_one_of_congr_mod_maximal
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  {m : ℕ}
  {ζ : B}
-- given
  (hpow : ζ ^ m = 1)
  (hcong : ζ - 1 ∈ IsLocalRing.maximalIdeal B)
  (hm_unit : (m : B) ∉ IsLocalRing.maximalIdeal B) :
-- imply
  ζ = 1 := by
-- proof
  have hS : (∑ i ∈ Finset.range m, ζ ^ i) * (ζ - 1) = 0 := by
    rw [geom_sum_mul, hpow, sub_self]
  have hpow_cong : ∀ n : ℕ, ζ ^ n - 1 ∈ IsLocalRing.maximalIdeal B := by
    intro n; induction n with
    | zero => simp
    | succ k ih =>
      have : ζ ^ (k + 1) - 1 = ζ * (ζ ^ k - 1) + (ζ - 1) := by ring
      rw [this]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ih) hcong
  obtain hS_zero | hζ_eq := mul_eq_zero.mp hS
  · exfalso; apply hm_unit
    have hmem : (m : B) - ∑ i ∈ Finset.range m, ζ ^ i ∈ IsLocalRing.maximalIdeal B := by
      rw [show (m : B) = ∑ _i ∈ Finset.range m, (1 : B) from by simp]
      rw [← Finset.sum_sub_distrib]
      apply Ideal.sum_mem
      intro i _
      have : -(ζ ^ i - 1) ∈ IsLocalRing.maximalIdeal B :=
        (IsLocalRing.maximalIdeal B).neg_mem (hpow_cong i)
      rwa [show -(ζ ^ i - 1) = 1 - ζ ^ i from by ring] at this
    rwa [hS_zero, sub_zero] at hmem
  · exact sub_eq_zero.mp hζ_eq

/--
[finite_field_adjoin_eq_top_of_isPrimitiveRoot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma finite_field_adjoin_eq_top_of_isPrimitiveRoot
  [Field k]
  [Field l]
  [Algebra k l]
  [Fintype l]
  {ζ : l}
-- given
  (hζ : IsPrimitiveRoot ζ (Fintype.card l - 1)) :
-- imply
  Algebra.adjoin k ({ζ} : Set l) = ⊤ := by
-- proof
  classical
  rw [Algebra.eq_top_iff]
  intro x
  by_cases hx : x = 0
  · subst hx; exact zero_mem _
  · have hζ_ne : ζ ≠ 0 := by
    intro h; rw [h] at hζ; exact absurd hζ.pow_eq_one
      (by simp [zero_pow (Nat.sub_pos_of_lt Fintype.one_lt_card).ne'])
    let ζ_unit : lˣ := Units.mk0 ζ hζ_ne
    let x_unit : lˣ := Units.mk0 x hx
    have hζ_unit : IsPrimitiveRoot ζ_unit (Fintype.card l - 1) := by
      constructor
      · ext; simp [ζ_unit, Units.val_pow_eq_pow_val, hζ.pow_eq_one]
      · intro d hd; apply hζ.dvd_of_pow_eq_one
        have : ((ζ_unit) ^ d : lˣ) = 1 := hd
        calc ζ ^ d = (ζ_unit : l) ^ d := by simp [ζ_unit]
          _ = ((ζ_unit ^ d : lˣ) : l) := by simp [Units.val_pow_eq_pow_val]
          _ = ((1 : lˣ) : l) := by rw [this]
          _ = 1 := rfl
    have hord : orderOf ζ_unit = Nat.card lˣ := by
      rwa [Nat.card_eq_fintype_card, Fintype.card_units]
    have hgen : Subgroup.zpowers ζ_unit = ⊤ := by
      apply Subgroup.eq_top_of_card_eq; rw [Nat.card_zpowers, hord]
    have hmem : x_unit ∈ Subgroup.zpowers ζ_unit := hgen ▸ Subgroup.mem_top _
    rw [← mem_powers_iff_mem_zpowers] at hmem
    obtain ⟨m, hm⟩ := hmem
    have hx_eq : x = ζ ^ m := by
      have := congr_arg Units.val hm
      simp [ζ_unit, x_unit, Units.val_pow_eq_pow_val] at this
      exact this.symm
    rw [hx_eq]
    exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton ζ)) m

/--
[dvr_unramified_cyclotomic_monogenic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma dvr_unramified_cyclotomic_monogenic
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [Fintype (IsLocalRing.ResidueField A)]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  {ζ_B : B}
-- given
  (hunr : IsDVRUnramified A B)
  (hζ_B : IsPrimitiveRoot ζ_B (Fintype.card (IsLocalRing.ResidueField A) ^ Module.finrank K L - 1)) :
-- imply
  Algebra.adjoin A ({ζ_B} : Set B) = ⊤ := by
-- proof
  set m := Fintype.card (IsLocalRing.ResidueField A) ^ Module.finrank K L - 1 with hm_def
  haveI : FiniteDimensional (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    IsLocalRing.ResidueField.finite_of_module_finite
  letI : Fintype (IsLocalRing.ResidueField B) := by
    haveI : Finite (IsLocalRing.ResidueField B) :=
      Module.finite_of_finite (IsLocalRing.ResidueField A)
    exact Fintype.ofFinite _
  have hm_unit : (m : B) ∉ IsLocalRing.maximalIdeal B := by
    intro hmem
    have hres_zero : (IsLocalRing.residue B) (m : B) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    have hres_eq : (IsLocalRing.residue B) (m : B) =
      ((m : ℕ) : IsLocalRing.ResidueField B) := map_natCast _ _
    rw [hres_eq] at hres_zero
    have hm_neg_one : ((m : ℕ) : IsLocalRing.ResidueField B) = -1 := by
      rw [hm_def]
      rw [Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos)]
      have hq : (Fintype.card (IsLocalRing.ResidueField A) :
        IsLocalRing.ResidueField B) = 0 := by
        rw [show (Fintype.card (IsLocalRing.ResidueField A) :
          IsLocalRing.ResidueField B) =
          algebraMap (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)
            (Fintype.card (IsLocalRing.ResidueField A) :
              IsLocalRing.ResidueField A) from
          (map_natCast _ _).symm]
        rw [Nat.cast_card_eq_zero, map_zero]
      simp [Nat.cast_pow, hq, zero_pow (Module.finrank_pos (R := K) (M := L)).ne']
    rw [hm_neg_one] at hres_zero
    exact one_ne_zero (neg_eq_zero.mp hres_zero)
  have hζ_res : IsPrimitiveRoot (IsLocalRing.residue B ζ_B) m := by
    constructor
    ·
      rw [← map_pow, hζ_B.pow_eq_one, map_one]
    ·
      intro d hd
      have hcong : ζ_B ^ d - 1 ∈ IsLocalRing.maximalIdeal B := by
        rw [← Ideal.Quotient.eq_zero_iff_mem]
        change (IsLocalRing.residue B) (ζ_B ^ d - 1) = 0
        simp only [map_sub, map_pow, map_one, hd, sub_self]
      have hpow : (ζ_B ^ d) ^ m = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hζ_B.pow_eq_one, one_pow]
      have := root_of_unity_eq_one_of_congr_mod_maximal hpow hcong hm_unit
      exact hζ_B.dvd_of_pow_eq_one d this
  have hcard : Fintype.card (IsLocalRing.ResidueField B) =
    Fintype.card (IsLocalRing.ResidueField A) ^ Module.finrank K L := by
    have efn := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing B K L
      (IsDiscreteValuationRing.not_a_field A)
    rw [hunr.ramIdx_eq_one, one_mul] at efn
    rw [← efn]
    have f_eq := inertiaDeg_algebraMap (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
    rwa [f_eq]
  rw [show m = Fintype.card (IsLocalRing.ResidueField B) - 1 from by omega] at hζ_res
  have hgen : Algebra.adjoin (IsLocalRing.ResidueField A)
    ({IsLocalRing.residue B ζ_B} : Set (IsLocalRing.ResidueField B)) = ⊤ :=
    finite_field_adjoin_eq_top_of_isPrimitiveRoot hζ_res
  exact dvr_monogenicity_unramified_forall A B
    hunr.residue_separable hunr.ramIdx_eq_one
    (IsLocalRing.residue B ζ_B) hgen ζ_B rfl

/--
[cor_10_17_integral_closure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma cor_10_17_integral_closure
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  [Fintype (IsLocalRing.ResidueField A)]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  {ζ : L}
-- given
  (hunr : IsDVRUnramified A B)
  (hζ : IsPrimitiveRoot ζ (Fintype.card (IsLocalRing.ResidueField A) ^ Module.finrank K L - 1))
  (hgen : IntermediateField.adjoin K ({ζ} : Set L) = ⊤) :
-- imply
  Algebra.adjoin A ({ζ} : Set L) = (IsScalarTower.toAlgHom A B L).range := by
-- proof
  set m := Fintype.card (IsLocalRing.ResidueField A) ^ Module.finrank K L - 1 with hm_def
  have hq : 1 < Fintype.card (IsLocalRing.ResidueField A) := Fintype.one_lt_card
  have hn : 0 < Module.finrank K L := Module.finrank_pos
  have hm_pos : 0 < m := by
    show 0 < Fintype.card (IsLocalRing.ResidueField A) ^ Module.finrank K L - 1
    have h1 : 1 < Fintype.card (IsLocalRing.ResidueField A) ^ Module.finrank K L := by
      calc Fintype.card (IsLocalRing.ResidueField A) ^ Module.finrank K L
        ≥ Fintype.card (IsLocalRing.ResidueField A) ^ 1 :=
          Nat.pow_le_pow_right (by omega) hn
        _ = Fintype.card (IsLocalRing.ResidueField A) := pow_one _
        _ > 1 := hq
    omega
  have hζ_integral : IsIntegral B ζ := by
    refine ⟨Polynomial.X ^ m - Polynomial.C 1, ?_, ?_⟩
    · exact Polynomial.Monic.sub_of_left (Polynomial.monic_X_pow m) (by simp [hm_pos])
    · simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow, hζ.pow_eq_one]
  obtain ⟨ζ_B, hζ_B_eq⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hζ_integral
  have hζ_B_prim : IsPrimitiveRoot ζ_B m := by
    have h : IsPrimitiveRoot ((algebraMap B L) ζ_B) m := hζ_B_eq ▸ hζ
    exact h.of_map_of_injective (IsFractionRing.injective B L)
  have h_adjoin_top : Algebra.adjoin A ({ζ_B} : Set B) = ⊤ :=
    dvr_unramified_cyclotomic_monogenic A K B L hunr ζ_B hζ_B_prim
  have h_image : (algebraMap B L) '' ({ζ_B} : Set B) = ({ζ} : Set L) := by
    simp [Set.image_singleton, hζ_B_eq]
  rw [← h_image, Algebra.adjoin_algebraMap A L ({ζ_B} : Set B), h_adjoin_top, Algebra.map_top]
end Cor_10_17
section Theorem_10_23
variable
  (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L] [IsFractionRing B L]
  [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]

/--
[AKLB_degree_eq_ramIdx_mul_resDeg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
lemma AKLB_degree_eq_ramIdx_mul_resDeg
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {B : Type*}
  [CommRing B]
  [IsDomain B]
  [IsDiscreteValuationRing B]
  [Algebra A B]
  [IsLocalHom (algebraMap A B)]
  [Module.Finite A B]
  [NoZeroSMulDivisors A B]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  [Algebra B L]
  [IsFractionRing B L]
  [Algebra A L]
  [IsScalarTower A B L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)] :
-- imply
  Module.finrank K L = AKLB_ramIdx A B * AKLB_resDeg A B := by
-- proof
  have hp : IsLocalRing.maximalIdeal A ≠ ⊥ := IsDiscreteValuationRing.not_a_field A
  have key := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing B K L hp
  rwa [Ideal.inertiaDeg_algebraMap] at key
end Theorem_10_23
end

/--
[integral_closure_isLocalRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
private lemma integral_closure_isLocalRing_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L] :
-- imply
  IsLocalRing ↥(integralClosure A L) := by
-- proof
  apply integral_closure_isLocalRing A K L

/--
[integral_closure_isNoetherianRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
private lemma integral_closure_isNoetherianRing_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable K L] :
-- imply
  IsNoetherianRing ↥(integralClosure A L) := by
-- proof
  apply integral_closure_isNoetherianRing A K L

/--
[integral_closure_module_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
private lemma integral_closure_module_finite_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable K L] :
-- imply
  Module.Finite A ↥(integralClosure A L) := by
-- proof
  apply integral_closure_module_finite A K L

/--
[thm_9_22_integralClosure_isDVR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
private lemma thm_9_22_integralClosure_isDVR_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {E : Type*}
  [Field E]
  [Algebra K E]
  [FiniteDimensional K E]
  [Algebra A E]
  [IsScalarTower A K E]
  [Algebra.IsSeparable K E] :
-- imply
  IsDiscreteValuationRing ↥(integralClosure A E) := by
-- proof
  apply thm_9_22_integralClosure_isDVR A K E

/--
[AKLB_intClE_isDVR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalExtensions.lean)
-/
@[path]
private lemma AKLB_intClE_isDVR_eq
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
  {L : Type*}
  [Field L]
  [Algebra K L]
  [FiniteDimensional K L]
  [Algebra A L]
  [IsScalarTower A K L]
  [Algebra.IsSeparable K L]
  {E : IntermediateField K L} :
-- imply
  IsDiscreteValuationRing ↥(integralClosure A ↥E) := by
-- proof
  apply AKLB_intClE_isDVR A K L E


-- created on 2026-10-23
