import Mathlib
import sympy.Basic
open IsLocalRing


private lemma isDomain_of_maximalIdeal_eq_span
  [CommRing L] [IsLocalRing L] [IsNoetherianRing L]
  {ϖ : L}
-- given
  (hreg : IsSMulRegular L ϖ)
  (hmax : maximalIdeal L = Ideal.span {ϖ}) :
-- imply
  IsDomain L := by
-- proof
  classical
  have hpow : ∀ n : ℕ, maximalIdeal L ^ n = Ideal.span {ϖ ^ n} := by
    intro n
    rw [hmax, Ideal.span_singleton_pow]
  have key : ∀ x : L, x ≠ 0 → ∃ (n : ℕ) (w : L), IsUnit w ∧ x = w * ϖ ^ n := by
    intro x hx
    have hex : ∃ n : ℕ, x ∉ maximalIdeal L ^ n := by
      by_contra h
      push Not at h
      apply hx
      have hmem : x ∈ ⨅ n : ℕ, maximalIdeal L ^ n := Ideal.mem_iInf.mpr h
      rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal L).ne_top,
        Ideal.mem_bot] at hmem
    have hn0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, Ideal.one_eq_top] at this
      apply this trivial
    obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := Nat.exists_eq_succ_of_ne_zero hn0
    have hxj : x ∈ maximalIdeal L ^ j := by
      have := Nat.find_min hex (m := j) (by omega)
      apply not_not.mp this
    have hxj1 : x ∉ maximalIdeal L ^ (j + 1) := hj ▸ Nat.find_spec hex
    rw [hpow] at hxj hxj1
    obtain ⟨w, rfl⟩ := Ideal.mem_span_singleton'.mp hxj
    refine ⟨j, w, ?_, rfl⟩
    by_contra hw
    apply hxj1
    have hw' : w ∈ maximalIdeal L := hw
    rw [hmax] at hw'
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw'
    apply Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩
  have : NoZeroDivisors L := ⟨fun {a b} hab => by
    by_contra h
    push Not at h
    obtain ⟨n, w, hw, rfl⟩ := key a h.1
    obtain ⟨m, w', hw', rfl⟩ := key b h.2
    apply (hw.mul hw').ne_zero ((hreg.pow (n + m)) (by show ϖ ^ (n + m) • (w * w') = ϖ ^ (n + m) • (0 : L); rw [smul_eq_mul, smul_zero, ← hab]; ring))⟩
  apply NoZeroDivisors.to_isDomain L


/--
[Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsStandardSmoothOfRelativeDimension_isDiscreteValuationRing_localization_atPrime.lean)
-/
@[path]
private lemma main
  {k : Type u} [Field k]
  {A : Type v} [CommRing A] [Algebra k A] [Algebra.IsStandardSmoothOfRelativeDimension 1 k A]
  {p : Ideal A} [p.IsMaximal] :
-- imply
  ∃ _ : IsDomain (Localization.AtPrime p), IsDiscreteValuationRing (Localization.AtPrime p) := by
-- proof
  classical
  obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial 1 k A
  let P := MvPolynomial (Fin 1) k
  let _ : Algebra P A := g.toRingHom.toAlgebra
  let _ : Algebra.Etale P A := hg
  let _ : IsScalarTower k P A := IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  let e : P ≃ₐ[k] Polynomial k := MvPolynomial.uniqueAlgEquiv k (Fin 1)
  let _ : IsPrincipalIdealRing P := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  have hPnf : ¬ IsField P := fun h => Polynomial.not_isField (R := k) (e.symm.toMulEquiv.isField h)
  let _ : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing P A
  let q : Ideal P := p.under P
  let _ : Algebra.FiniteType k A :=
    (inferInstance : Algebra.FiniteType k P).trans (inferInstance : Algebra.FiniteType P A)
  let _ : Field (A ⧸ p) := Ideal.Quotient.field p
  let _ : Module.Finite k (A ⧸ p) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ p)
  let _ : Module.Finite k (P ⧸ q) :=
    FiniteDimensional.of_injective (IsScalarTower.toAlgHom k (P ⧸ q) (A ⧸ p)).toLinearMap
      (FaithfulSMul.algebraMap_injective (P ⧸ q) (A ⧸ p))
  let _ : q.IsMaximal := by
    refine Ideal.Quotient.maximal_of_isField _ ?_
    let _ : Algebra.IsIntegral k (P ⧸ q) := Algebra.IsIntegral.of_finite k _
    apply isField_of_isIntegral_of_isField' (R := k) (S := P ⧸ q) (Field.toIsField k)
  have hq0 : q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField (inferInstance : q.IsMaximal) hPnf
  obtain ⟨π, hπ⟩ := (IsPrincipalIdealRing.principal q).principal
  have hπ0 : π ≠ 0 := by
    intro h
    subst h
    apply hq0
    rw [hπ]
    simp
  set L := Localization.AtPrime p
  let _ := Localization.AtPrime.algebraOfLiesOver q p
  have hmap : q.map (algebraMap P L) = maximalIdeal L :=
    ((Algebra.isUnramifiedAt_iff_map_eq (R := P) (p := q) (q := p)).mp inferInstance).2
  have hmaxL : maximalIdeal L = Ideal.span {algebraMap P L π} := by
    rw [← hmap, hπ]
    change Ideal.map (algebraMap P L) (Ideal.span {π}) = _
    rw [Ideal.map_span, Set.image_singleton]
  let _ : Module.Flat P L := Module.Flat.trans P A L
  have hreg : IsSMulRegular L (algebraMap P L π) := by
    have h : IsSMulRegular L π :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ0)
    intro a b hab
    apply h
    simpa [Algebra.smul_def] using hab
  have hne : maximalIdeal L ≠ ⊥ := by
    rw [hmaxL, Ne, Ideal.span_singleton_eq_bot]
    intro h0
    have : (algebraMap P L π) • (1 : L) = (algebraMap P L π) • (0 : L) := by
      simp [h0]
    apply one_ne_zero (hreg this)
  have hnf : ¬ IsField L := fun hF => hne ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)
  let _ : IsDomain L := isDomain_of_maximalIdeal_eq_span hreg hmaxL
  have hprinc : (maximalIdeal L).IsPrincipal := ⟨⟨algebraMap P L π, hmaxL⟩⟩
  refine ⟨inferInstance, ?_⟩
  apply ((IsDiscreteValuationRing.TFAE L hnf).out 5 1).mp hprinc


-- created on 2026-10-13
