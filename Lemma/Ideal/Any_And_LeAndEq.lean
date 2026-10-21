import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private lemma isJacobsonRing_of_field
  {K : Type u} [Field K] :
  -- imply
  IsJacobsonRing K := by
  -- proof
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  have hPbot : P = ⊥ := by
    obtain h | h := Ideal.eq_bot_or_top P
    · apply h
    · apply absurd h hP.ne_top
  subst hPbot
  refine le_antisymm ?_ Ideal.le_jacobson
  apply sInf_le ⟨le_rfl, Ideal.bot_isMaximal⟩

private lemma mem_of_forall_isMaximal_mem
  {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  {𝔪₀ : Ideal R} [𝔪₀.IsMaximal]
  {𝔮 : Ideal A} [𝔮.IsPrime]
  {a : A}
  -- given
  (h𝔮 : Ideal.map (algebraMap R A) 𝔪₀ ≤ 𝔮)
  (ha : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔮 ≤ 𝔪 → a ∈ 𝔪) :
  -- imply
  a ∈ 𝔮 := by
  -- proof
  classical
  have hcm : 𝔮.comap (algebraMap R A) = 𝔪₀ := by
    apply ((Ideal.IsMaximal.eq_of_le inferInstance (Ideal.comap_ne_top _ Ideal.IsPrime.ne_top') _)).symm
    rw [← Ideal.map_le_iff_le_comap]
    apply h𝔮
  let _ : (𝔮.comap (algebraMap R A)).IsMaximal := hcm ▸ inferInstance
  let _ : Field (R ⧸ 𝔮.comap (algebraMap R A)) := Ideal.Quotient.field _
  let _ : IsJacobsonRing (R ⧸ 𝔮.comap (algebraMap R A)) := isJacobsonRing_of_field _
  let _ : Algebra.FiniteType R (A ⧸ 𝔮) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ R 𝔮) (Ideal.Quotient.mkₐ_surjective R 𝔮)
  let _ : Algebra.FiniteType (R ⧸ 𝔮.comap (algebraMap R A)) (A ⧸ 𝔮) := Algebra.FiniteType.of_restrictScalars_finiteType R (R ⧸ 𝔮.comap (algebraMap R A)) (A ⧸ 𝔮)
  let hJ : IsJacobsonRing (A ⧸ 𝔮) := isJacobsonRing_of_finiteType (A := R ⧸ 𝔮.comap (algebraMap R A))
  have hbot : (⊥ : Ideal (A ⧸ 𝔮)).jacobson = ⊥ := Iff.mp isJacobsonRing_iff_prime_eq hJ ⊥ Ideal.isPrime_bot
  have hmk : Ideal.Quotient.mk 𝔮 a ∈ (⊥ : Ideal (A ⧸ 𝔮)).jacobson := by
    rw [Ideal.jacobson, Ideal.mem_sInf]
    rintro M ⟨-, hM⟩
    apply ha _ (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective) _
    intro x hx
    rw [Ideal.mem_comap, Iff.mpr Ideal.Quotient.eq_zero_iff_mem hx]
    apply M.zero_mem
  rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmk
  apply hmk

/--
[Ideal_exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Ideal_exists_isMaximal_forall_mem_minimalPrimes_le_imp_eq_of_finiteType.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsNoetherianRing R]
  {A : Type v} [CommRing A] [Algebra R A] [Algebra.FiniteType R A]
  {𝔪₀ : Ideal R} [𝔪₀.IsMaximal]
  {I 𝔮 : Ideal A}
  -- given
  (hI : Ideal.map (algebraMap R A) 𝔪₀ ≤ I)
  (h𝔮 : 𝔮 ∈ I.minimalPrimes)
  (_ : ¬ 𝔮.IsMaximal)
  (_ : ∀ P : Ideal A, P.IsPrime → 𝔮 < P → P.IsMaximal) :
  -- imply
  ∃ 𝔪 : Ideal A, 𝔪.IsMaximal ∧ 𝔮 ≤ 𝔪 ∧ ∀ 𝔮' ∈ I.minimalPrimes, 𝔮' ≤ 𝔪 → 𝔮' = 𝔮 := by
  -- proof
  classical
  let h𝔮p : 𝔮.IsPrime := h𝔮.1.1
  have hI𝔮 : I ≤ 𝔮 := h𝔮.1.2
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing A I
  let S : Finset (Ideal A) := hfin.toFinset.erase 𝔮
  have hS : ∀ 𝔮' ∈ S, 𝔮' ∈ I.minimalPrimes ∧ 𝔮' ≠ 𝔮 := by
    intro 𝔮' h
    rw [Finset.mem_erase, Set.Finite.mem_toFinset] at h
    exact ⟨h.2, h.1⟩
  by_contra hcon
  have hbad : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔮 ≤ 𝔪 → ∃ 𝔮' ∈ S, 𝔮' ≤ 𝔪 := by
    intro 𝔪 h𝔪 hle
    by_contra hno
    apply hcon
    refine ⟨𝔪, h𝔪, hle, fun 𝔮' h𝔮' hle' => ?_⟩
    by_contra hne
    apply hno
    refine ⟨𝔮', ?_, hle'⟩
    rw [Finset.mem_erase, Set.Finite.mem_toFinset]
    exact ⟨hne, h𝔮'⟩
  let J : Ideal A := ∏ 𝔮' ∈ S, 𝔮'
  have hJle : ∀ 𝔮' ∈ S, J ≤ 𝔮' := fun 𝔮' h => Ideal.prod_le_inf.trans (Finset.inf_le h)
  have hJ𝔮 : J ≤ 𝔮 := by
    intro a haJ
    refine mem_of_forall_isMaximal_mem (hI.trans hI𝔮) ?_
    intro 𝔪 h𝔪 hle
    obtain ⟨𝔮', h𝔮'S, h𝔮'𝔪⟩ := hbad 𝔪 h𝔪 hle
    apply h𝔮'𝔪 (hJle 𝔮' h𝔮'S haJ)
  obtain ⟨𝔮', h𝔮'S, h𝔮'le⟩ := Iff.mp (Ideal.IsPrime.prod_le h𝔮p) hJ𝔮
  obtain ⟨h𝔮'min, hne⟩ := hS 𝔮' h𝔮'S
  apply hne
  apply le_antisymm h𝔮'le (h𝔮.2 ⟨h𝔮'min.1.1, h𝔮'min.1.2⟩ h𝔮'le)


-- created on 2026-10-21
