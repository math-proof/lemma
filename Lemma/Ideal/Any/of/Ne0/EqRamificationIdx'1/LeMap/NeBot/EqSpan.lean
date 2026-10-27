import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped Pointwise
open IsDedekindDomain WithZero


/-- ported from external source -/
@[path]
private lemma main
  {A : Type u} [CommRing A] [IsDedekindDomain A]
  {B : Type u} [CommRing B] [IsDedekindDomain B] [Algebra A B]
  {p : Ideal A} [p.IsMaximal]
  {q : Ideal B} [q.IsMaximal]
  {L : Type u} [Field L] [Algebra B L] [IsFractionRing B L] [Algebra A L] [IsScalarTower A B L]
  {π : A}
  {z : L}
-- given
  (hp : p = Ideal.span {π})
  (hq : q ≠ ⊥)
  (hpq : Ideal.map (algebraMap A B) p ≤ q)
  (he : Ideal.ramificationIdx' p q = 1)
  (hz : z ≠ 0) :
-- imply
  ∃ (n : ℤ) (b s : B), b ∉ q ∧ s ∉ q ∧
      z * (algebraMap B L s) = (algebraMap A L π) ^ n * algebraMap B L b := by
  classical
    let v : HeightOneSpectrum B := ⟨q, inferInstance, hq⟩
    have hv : v.asIdeal = q := rfl
    set πB : B := algebraMap A B π with hπB
    have hmap : Ideal.map (algebraMap A B) p = Ideal.span {πB} := by
-- proof
      rw [hp, Ideal.map_span, Set.image_singleton]
    have hπB0 : πB ≠ 0 := by
      intro h0
      have hbot : Ideal.map (algebraMap A B) p = ⊥ := by rw [hmap, h0, Ideal.span_singleton_eq_bot]
      have : Ideal.ramificationIdx' p q = 0 :=
        Ideal.ramificationIdx_eq_zero (fun n => ⟨n + 1, by rw [hbot]; apply bot_le, Nat.lt_succ_self n⟩)
      omega
    have hmap0 : Ideal.map (algebraMap A B) p ≠ ⊥ := by
      rwa [hmap, Ne, Ideal.span_singleton_eq_bot]
    have hvπ : v.intValuation πB = exp (-1 : ℤ) := by
      rw [v.intValuation_eq_exp_neg_multiplicity hπB0, hv, ← hmap,
        ← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap0 (inferInstance : q.IsPrime), he]
      rfl
    have hπL : algebraMap A L π = algebraMap B L πB := by
      rw [hπB, ← IsScalarTower.algebraMap_apply]
    have hwπ : v.valuation L (algebraMap A L π) = exp (-1 : ℤ) := by
      rw [hπL, HeightOneSpectrum.valuation_of_algebraMap, hvπ]
    have hπL0 : algebraMap A L π ≠ 0 := by
      rw [hπL]; apply (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hπB0
    have hwz0 : v.valuation L z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz
    set k : ℤ := log (v.valuation L z) with hk
    have hwz : v.valuation L z = exp k := by rw [hk, exp_log hwz0]
    set y : L := z * (algebraMap A L π) ^ k with hy
    have hwy : v.valuation L y = 1 := by
      rw [hy, map_mul, map_zpow₀, hwz, hwπ, ← exp_zsmul, ← exp_add]
      simp
    obtain ⟨b, ⟨s, hs⟩, hbs⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v y hwy.le
    have hs' : s ∉ q := hs
    have hws : v.valuation L (algebraMap B L s) = 1 := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (v.intValuation_eq_one_iff_mem_primeCompl s).mpr hs
    have hb' : b ∉ q := by
      have hwb : v.valuation L (algebraMap B L b) = 1 := by rw [← hbs, map_mul, hwy, hws, one_mul]
      rw [HeightOneSpectrum.valuation_of_algebraMap] at hwb
      exact (v.intValuation_eq_one_iff_mem_primeCompl b).mp hwb
    refine ⟨-k, b, s, hb', hs', ?_⟩
    rw [← hbs, hy, zpow_neg]
    field_simp


-- created on 2026-10-23
