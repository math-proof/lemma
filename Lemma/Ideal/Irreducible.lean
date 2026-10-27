import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Polynomial_irreducible_cyclotomic_fractionRing_of_maximalIdeal_eq_span](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_irreducible_cyclotomic_fractionRing_of_maximalIdeal_eq_span.lean)
-/
@[path]
private lemma main
  (A₀ : Type) [CommRing A₀] [IsDomain A₀] [IsDiscreteValuationRing A₀] (q : ℕ) [Fact q.Prime]
  (hA₀q : IsLocalRing.maximalIdeal A₀ = Ideal.span {(q : A₀)}) :
  -- imply
  Irreducible (Polynomial.cyclotomic q (FractionRing A₀)) := by
  -- proof
  classical
  have hqP : q.Prime := Fact.out
  have hq0 : (q : A₀) ≠ 0 := by
    intro h
    apply IsDiscreteValuationRing.not_a_field A₀
    rw [hA₀q, h]
    apply Ideal.span_singleton_eq_bot.mpr rfl
  have hqm : (q : A₀) ∈ IsLocalRing.maximalIdeal A₀ := by rw [hA₀q]; apply Ideal.mem_span_singleton_self _
  have hqnu : ¬ IsUnit (q : A₀) := (IsLocalRing.mem_maximalIdeal _).mp hqm
  have hMtop : (IsLocalRing.maximalIdeal A₀) ≠ ⊤ := Ideal.IsMaximal.ne_top inferInstance
  set g : Polynomial ℤ := (Polynomial.cyclotomic q ℤ).comp (Polynomial.X + 1) with hg
  set f : Polynomial A₀ := (Polynomial.cyclotomic q A₀).comp (Polynomial.X + 1) with hf
  have hfg : f = g.map (Int.castRingHom A₀) := by
    simp only [hf, hg, Polynomial.map_comp, Polynomial.map_cyclotomic, Polynomial.map_add, Polynomial.map_X, Polynomial.map_one]
  have hgmon : g.Monic := by
    rw [hg, show (Polynomial.X + 1 : Polynomial ℤ) = Polynomial.X + Polynomial.C 1 by simp]
    apply (Polynomial.cyclotomic.monic q ℤ).comp (Polynomial.monic_X_add_C 1) fun h => by
      rw [Polynomial.natDegree_X_add_C] at h
      apply zero_ne_one h.symm
  have hfmon : f.Monic := by rw [hfg]; apply hgmon.map _
  have hdeg : f.natDegree = g.natDegree := by rw [hfg]; apply hgmon.natDegree_map _
  have hgE := cyclotomic_comp_X_add_one_isEisensteinAt q
  have hleading : f.leadingCoeff ∉ IsLocalRing.maximalIdeal A₀ := by
    rw [hfmon.leadingCoeff]
    apply (Ideal.ne_top_iff_one (IsLocalRing.maximalIdeal A₀)).mp hMtop
  have hmem : ∀ {n : ℕ}, n < f.natDegree → f.coeff n ∈ IsLocalRing.maximalIdeal A₀ := fun {n} hn => by
    have hn' : n < g.natDegree := hdeg ▸ hn
    have hcoeff := hgE.mem hn'
    rw [Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hcoeff
    obtain ⟨c, hc⟩ := hcoeff
    rw [hfg, Polynomial.coeff_map, hc, map_mul, hA₀q]
    refine Ideal.mul_mem_right _ _ ?_
    simp
  have hnot : f.coeff 0 ∉ IsLocalRing.maximalIdeal A₀ ^ 2 := by
    have h0 : f.coeff 0 = (q : A₀) := by
      rw [Polynomial.coeff_zero_eq_eval_zero, hf, Polynomial.eval_comp]
      simp [Polynomial.eval_one_cyclotomic_prime]
    rw [h0, hA₀q, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    rintro ⟨c, hc⟩
    apply hqnu
    have h1 : (q : A₀) * (1 - (q : A₀) * c) = 0 := by linear_combination hc
    obtain h | h := mul_eq_zero.mp h1
    ·
      apply absurd h hq0
    ·
      apply isUnit_iff_exists_inv.mpr ⟨c, by linear_combination (-1 : A₀) * h⟩
  have hfE : f.IsEisensteinAt (IsLocalRing.maximalIdeal A₀) := { leading := hleading, mem := hmem, notMem := hnot }
  have hfdeg : 0 < f.natDegree := by
    rw [hdeg, hg, Polynomial.natDegree_comp, show (Polynomial.X + 1 : Polynomial ℤ) = Polynomial.X + Polynomial.C 1 by simp, Polynomial.natDegree_X_add_C, mul_one, Polynomial.natDegree_cyclotomic, Nat.totient_prime hqP]
    have := hqP.two_le
    omega
  have hfirr : Irreducible f := hfE.irreducible (Ideal.IsMaximal.isPrime inferInstance) hfmon.isPrimitive hfdeg
  have hFirr : Irreducible (f.map (algebraMap A₀ (FractionRing A₀))) :=
    (hfmon.irreducible_iff_irreducible_map_fraction_map).mp hfirr
  have hmap : f.map (algebraMap A₀ (FractionRing A₀)) = Polynomial.algEquivAevalXAddC (1 : FractionRing A₀) (Polynomial.cyclotomic q (FractionRing A₀)) := by
    rw [hf, Polynomial.map_comp, Polynomial.map_cyclotomic]
    simp [Polynomial.algEquivAevalXAddC, Polynomial.comp_eq_aeval]
  rw [hmap] at hFirr
  apply (MulEquiv.irreducible_iff (Polynomial.algEquivAevalXAddC (1 : FractionRing A₀))).mp hFirr


-- created on 2026-10-20
