import Mathlib
import Initialize.Tactic.Attr.Basic
open IsDedekindDomain


/--
[IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDedekindDomain_HeightOneSpectrum_finite_residueField_adicCompletionIntegers.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDedekindDomain R]
  {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R} [Finite (R ⧸ v.asIdeal)] :
-- imply
  Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
-- proof
  classical
    have hv : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Integers (v.adicCompletionIntegers K) :=
      Valuation.valuationSubring.integers _
    have step1 : ∀ k : K, v.valuation K k ≤ 1 → ∃ r : R, v.valuation K (k - algebraMap R K r) < 1 := by
      intro k hk
      have hkmem : k ∈ (v.valuation K).valuationSubring := hk
      rw [← IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at hkmem
      obtain ⟨a, s, hs, rfl⟩ : ∃ (a s : R) (_ : s ∈ v.asIdeal.primeCompl), k = algebraMap R K a * (algebraMap R K s)⁻¹ := hkmem
      have hs' : s ∉ v.asIdeal := hs
      have := v.isMaximal
      let := Ideal.Quotient.field v.asIdeal
      obtain ⟨t, ht⟩ : ∃ t : R, s * t - 1 ∈ v.asIdeal := by
        have hs0 : (Ideal.Quotient.mk v.asIdeal s) ≠ 0 := by
          rwa [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
        obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective ((Ideal.Quotient.mk v.asIdeal s)⁻¹)
        refine ⟨t, ?_⟩
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, ht, mul_inv_cancel₀ hs0, sub_self]
      refine ⟨a * t, ?_⟩
      have hvs : v.valuation K (algebraMap R K s) = 1 := by
        rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
        apply (IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff).2 hs'
      have hs0K : algebraMap R K s ≠ 0 := by
        intro h; rw [h, map_zero] at hvs; exact zero_ne_one hvs
      have hrw : algebraMap R K a * (algebraMap R K s)⁻¹ - algebraMap R K (a * t) =
          algebraMap R K a * (algebraMap R K s)⁻¹ * (1 - algebraMap R K (s * t)) := by
        rw [map_mul, map_mul]; field_simp
      rw [hrw, map_mul, map_mul, map_inv₀, hvs, inv_one, mul_one]
      calc
        _ ≤ 1 * v.valuation K (1 - algebraMap R K (s * t)) := by
          gcongr; exact v.valuation_le_one a
        _ < 1 := by
          have ht' : 1 - s * t ∈ v.asIdeal := by rw [← neg_sub]; exact v.asIdeal.neg_mem ht
          rwa [one_mul, ← map_one (algebraMap R K), ← map_sub, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    let ψ : R →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
      (IsLocalRing.residue (v.adicCompletionIntegers K)).comp (algebraMap R (v.adicCompletionIntegers K))
    have hψ : Function.Surjective ψ := by
      intro xbar
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective xbar
      have hopen : IsOpen {y : v.adicCompletion K | Valued.v (y - x) < 1} := by
        rw [isOpen_iff_mem_nhds]
        intro y hy
        rw [Valued.mem_nhds]
        refine ⟨1, fun z hz => ?_⟩
        have hz' : Valued.v (z - y) < 1 := by
          have h := hz
          simp only [Set.mem_ofPred_eq, Units.val_one] at h
          exact (Valuation.restrict_lt_one_iff Valued.v).1 h
        show Valued.v (z - x) < 1
        calc
          _ = Valued.v (z - y + (y - x)) := by rw [sub_add_sub_cancel]
          _ ≤ max (Valued.v (z - y)) (Valued.v (y - x)) := Valuation.map_add _ _ _
          _ < 1 := max_lt hz' hy
      obtain ⟨k, hk⟩ := (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap K v).exists_mem_open hopen
        ⟨x, by simp⟩
      have hk' : Valued.v (algebraMap K (v.adicCompletion K) k - (x : v.adicCompletion K)) < 1 := hk
      have hcoeK : ∀ k : K, Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k := fun k =>
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
      have hkv : Valued.v (algebraMap K (v.adicCompletion K) k) = v.valuation K k := hcoeK k
      have hk1 : v.valuation K k ≤ 1 := by
        rw [← hkv]
        calc
          _ = Valued.v (algebraMap K (v.adicCompletion K) k - x + x) := by rw [sub_add_cancel]
          _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) k - x)) (Valued.v (x : v.adicCompletion K)) := Valuation.map_add _ _ _
          _ ≤ 1 := max_le hk'.le x.2
      obtain ⟨r, hr⟩ := step1 k hk1
      refine ⟨r, ?_⟩
      show IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) = IsLocalRing.residue _ x
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        hv.isUnit_iff_valuation_eq_one]
      apply ne_of_lt
      have hcoe : (((algebraMap R (v.adicCompletionIntegers K) r - x : v.adicCompletionIntegers K) : v.adicCompletion K)) =
          algebraMap K (v.adicCompletion K) (algebraMap R K r) - (x : v.adicCompletion K) := by
        rw [AddSubgroupClass.coe_sub, IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
        rfl
      show Valued.v (((algebraMap R (v.adicCompletionIntegers K) r - x : v.adicCompletionIntegers K) : v.adicCompletion K)) < 1
      rw [hcoe]
      have hrk : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) - algebraMap K (v.adicCompletion K) k) < 1 := by
        rwa [← map_sub, hcoeK, ← neg_sub, Valuation.map_neg]
      calc
        _ = Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) - algebraMap K (v.adicCompletion K) k +
            (algebraMap K (v.adicCompletion K) k - x)) := by rw [sub_add_sub_cancel]
        _ ≤ max (Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r) - algebraMap K (v.adicCompletion K) k))
          (Valued.v (algebraMap K (v.adicCompletion K) k - x)) := Valuation.map_add _ _ _
        _ < 1 := max_lt hrk hk'
    have : Finite (R ⧸ v.asIdeal) := inferInstance
    have hker : ∀ r ∈ v.asIdeal, ψ r = 0 := by
      intro r hr
      show IsLocalRing.residue _ (algebraMap R (v.adicCompletionIntegers K) r) = 0
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        hv.isUnit_iff_valuation_eq_one]
      apply ne_of_lt
      show Valued.v ((algebraMap R (v.adicCompletionIntegers K) r : v.adicCompletionIntegers K) : v.adicCompletion K) < 1
      rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
      show Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) < 1
      have h1 : Valued.v (algebraMap K (v.adicCompletion K) (algebraMap R K r)) = v.valuation K (algebraMap R K r) :=
        IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
      rwa [h1, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
    let ψbar : R ⧸ v.asIdeal →+* IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
      Ideal.Quotient.lift v.asIdeal ψ hker
    refine Finite.of_surjective ψbar fun y => ?_
    obtain ⟨r, rfl⟩ := hψ y
    exact ⟨Ideal.Quotient.mk _ r, rfl⟩


-- created on 2026-10-23
