import Mathlib
import Initialize.Tactic.Attr.Basic
open IsDedekindDomain


/--
[ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_eq_valuationSubringAtPrime_of_forall_algebraMap_mem.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {V : ValuationSubring K}
-- given
  (hRV : ∀ r : R, algebraMap R K r ∈ V)
  (hV : V ≠ ⊤) :
-- imply
  ∃ v : HeightOneSpectrum R, V = v.valuationSubringAtPrime K ∧
      ∀ r : R, r ∈ v.asIdeal ↔ algebraMap R K r ∈ V.nonunits := by
-- proof
  classical
    let 𝔭 : Ideal R :=
      { carrier := {r | V.valuation (algebraMap R K r) < 1}
        zero_mem' := by simp
        add_mem' := fun {a b} ha hb => by
          simp only [Set.mem_setOf_eq, map_add] at *
          exact Valuation.map_add_lt _ ha hb
        smul_mem' := fun c r hr => by
          simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
          calc
            _ ≤ 1 * V.valuation (algebraMap R K r) := by
              gcongr; exact (V.valuation_le_one_iff _).mpr (hRV c)
            _ < 1 := by rwa [one_mul] }
    have hmem𝔭 : ∀ r : R, r ∈ 𝔭 ↔ V.valuation (algebraMap R K r) < 1 := fun r => Iff.rfl
    have h𝔭prime : 𝔭.IsPrime := by
      refine ⟨?_, ?_⟩
      ·
        rw [Ideal.ne_top_iff_one]; simp [hmem𝔭]
      ·
        intro a b hab
        rw [hmem𝔭, map_mul, map_mul] at hab
        by_contra hcon
        push Not at hcon
        rw [hmem𝔭, hmem𝔭, not_lt, not_lt] at hcon
        have ha : V.valuation (algebraMap R K a) = 1 := le_antisymm ((V.valuation_le_one_iff _).mpr (hRV a)) hcon.1
        have hb : V.valuation (algebraMap R K b) = 1 := le_antisymm ((V.valuation_le_one_iff _).mpr (hRV b)) hcon.2
        rw [ha, hb, one_mul] at hab
        exact lt_irrefl _ hab
    have h𝔭bot : 𝔭 ≠ ⊥ := by
      intro hbot
      apply hV
      refine top_le_iff.mp fun x _ => ?_
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
      have hbV : V.valuation (algebraMap R K b) = 1 := by
        refine le_antisymm ((V.valuation_le_one_iff _).mpr (hRV b)) (not_lt.mp fun hlt => ?_)
        have : b ∈ 𝔭 := hlt
        rw [hbot, Ideal.mem_bot] at this
        exact nonZeroDivisors.ne_zero hb this
      rw [← V.valuation_le_one_iff, map_div₀, hbV, div_one]
      exact (V.valuation_le_one_iff _).mpr (hRV a)
    let v : HeightOneSpectrum R := ⟨𝔭, h𝔭prime, h𝔭bot⟩
    refine ⟨v, ?_, fun r => ?_⟩
    ·
      set W := v.valuationSubringAtPrime K with hW
      have hWV : W ≤ V := by
        intro x hx
        have hx' : x ∈ W.toSubring := hx
        rw [hW, HeightOneSpectrum.valuationSubringAtPrime_toSubring, Subalgebra.mem_toSubring] at hx'
        have hx'' : ∃ a s : R, ∃ _ : s ∈ v.asIdeal.primeCompl, x = algebraMap R K a * (algebraMap R K s)⁻¹ := hx'
        obtain ⟨a, s, hs, rfl⟩ := hx''
        have hsV : V.valuation (algebraMap R K s) = 1 := by
          refine le_antisymm ((V.valuation_le_one_iff _).mpr (hRV s)) (not_lt.mp fun hlt => hs ?_)
          exact hlt
        rw [← V.valuation_le_one_iff, map_mul, map_inv₀, hsV, inv_one, mul_one]
        exact (V.valuation_le_one_iff _).mpr (hRV a)
      have key := ValuationSubring.ofPrime_idealOfLE W V hWV
      set Q := W.idealOfLE V hWV with hQ
      have : Q.IsPrime := by rw [hQ, ValuationSubring.idealOfLE]; infer_instance
      obtain hQbot | hQbot := eq_or_ne Q ⊥
      ·
        exfalso; apply hV
        rw [← key]
        exact (ValuationSubring.ofPrime.congr_simp W Q ⊥ hQbot).trans (ValuationSubring.ofPrime_bot W)
      ·
        have hQmax : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQbot
        have hQeq : Q = IsLocalRing.maximalIdeal W := IsLocalRing.eq_maximalIdeal hQmax
        rw [← key]
        exact (ValuationSubring.ofPrime.congr_simp W Q _ hQeq).trans (ValuationSubring.ofPrime_top W)
    ·
      rw [ValuationSubring.mem_nonunits_iff]; exact hmem𝔭 r


-- created on 2026-10-23
