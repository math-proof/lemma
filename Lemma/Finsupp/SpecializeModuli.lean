import Mathlib
import Theorem.HahnSeries.JqCoeff
import Theorem.Ideal.RatFuncPlaces
import Abbrev.ModularCurve_SpecializeModuli

namespace ModularCurve

private theorem jqModC_pow (K : Type*) [CommRing K] (n : ℕ) :
    (jqModC K) ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((jNum.map (Int.castRingHom K)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

private theorem constantCoeff_jNum_map (K : Type*) [CommRing K] :
    PowerSeries.constantCoeff (jNum.map (Int.castRingHom K)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum, map_one]

private theorem jqModC_pow_coeff_self (K : Type*) [CommRing K] (n : ℕ) :
    ((jqModC K) ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNum_map, one_pow]

private theorem jqModC_pow_coeff_of_lt (K : Type*) [CommRing K] {n : ℕ} {m : ℤ}
    (hm : m < -(n : ℤ)) : ((jqModC K) ^ n).coeff m = 0 := by
  rw [jqModC_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

private theorem algebraMap_laurentSeries_eq_single (K : Type*) [CommRing K] (c : K) :
    algebraMap K (LaurentSeries K) c = HahnSeries.single 0 c := by
  have h1 : algebraMap K (PowerSeries K) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

private theorem aeval_jqModC_eq_zero {K : Type*} [CommRing K] {p : Polynomial K}
    (hp : Polynomial.aeval (jqModC K) p = 0) : p = 0 := by
  by_contra hp0
  set n := p.natDegree with hn
  have hcoeff : (Polynomial.aeval (jqModC K) p).coeff (-(n : ℤ)) = p.coeff n := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
      Finset.sum_eq_single n]
    · rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
        jqModC_pow_coeff_self, mul_one]
    · intro i hi hin
      have hilt : i < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
      rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul,
        jqModC_pow_coeff_of_lt, mul_zero]
      omega
    · intro hn'
      exact absurd (Finset.self_mem_range_succ n) hn'
  rw [hp] at hcoeff
  simp only [HahnSeries.coeff_zero] at hcoeff
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hcoeff.symm)

theorem transcendental_jqModC (K : Type*) [Field K] : Transcendental K (jqModC K) :=
  transcendental_iff.mpr fun _ hp => aeval_jqModC_eq_zero hp

end ModularCurve

set_option autoImplicit false

noncomputable section

open AlgebraicCurve Ideal

namespace ModularCurve

section Transcendence

variable (K : Type*) [Field K]

def ratFuncEquivCharLOneC : RatFunc K ≃ₐ[K] (modularFunctionFieldC K 1) :=
  (RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K)).trans
    (IntermediateField.equivOfEq (modularFunctionFieldC_one K).symm)

end Transcendence

section Jacobian

variable (K : Type*) [Field K]

def charLGeomPlaceEquiv :
    Place K (RatFunc K) ≃ Place K (modularFunctionFieldC K 1) :=
  Place.congrEquiv (ratFuncEquivCharLOneC K).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC K).commutes a)

def charLGeomPlaceOfPoint (a : K) : Place K (modularFunctionFieldC K 1) :=
  charLGeomPlaceEquiv K (RationalFunctionField.placeOfPoint K a)

theorem charLGeomPlaceOfPoint_injective : Function.Injective (charLGeomPlaceOfPoint K) :=
  fun _ _ h => RationalFunctionField.placeOfPoint_injective K
    ((charLGeomPlaceEquiv K).injective h)

theorem deg_charLGeomPlaceOfPoint (a : K) : (charLGeomPlaceOfPoint K a).deg = 1 :=
  (Place.deg_congrRingEquiv (ratFuncEquivCharLOneC K).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC K).commutes a)
    (RationalFunctionField.placeOfPoint K a)).trans
    (RationalFunctionField.deg_placeOfPoint K a)

def charLGeomModuliDictionary :
    (K →₀ ℤ) →+ Divisor K (modularFunctionFieldC K 1) :=
  Finsupp.mapDomain.addMonoidHom (charLGeomPlaceOfPoint K)

theorem charLGeomModuliDictionary_injective :
    Function.Injective (charLGeomModuliDictionary K) :=
  Finsupp.mapDomain_injective (charLGeomPlaceOfPoint_injective K)

@[simp]
theorem charLGeomModuliDictionary_single (a : K) (n : ℤ) :
    charLGeomModuliDictionary K (Finsupp.single a n)
      = Finsupp.single (charLGeomPlaceOfPoint K a) n := by
  simp only [charLGeomModuliDictionary, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapDomain_single]

end Jacobian

section Map

variable {K k : Type*} [Field K] [Field k]

def specializePlace (r : K → k) (a : K) : Place k (modularFunctionFieldC k 1) :=
  charLGeomPlaceOfPoint k (r a)

omit [Field K] in
@[simp]
theorem specializePlace_def (r : K → k) (a : K) :
    specializePlace r a = charLGeomPlaceOfPoint k (r a) := rfl

omit [Field K] in

theorem deg_specializePlace (r : K → k) (a : K) : (specializePlace r a).deg = 1 :=
  deg_charLGeomPlaceOfPoint k (r a)

omit [Field K] in

theorem specializePlace_eq_of_eq (r : K → k) {a b : K} (h : r a = r b) :
    specializePlace r a = specializePlace r b := by
  simp only [specializePlace, h]

omit [Field K] in

theorem specializePlace_inj_iff (r : K → k) {a b : K} :
    specializePlace r a = specializePlace r b ↔ r a = r b :=
  ⟨fun h => charLGeomPlaceOfPoint_injective k h, specializePlace_eq_of_eq r⟩

def specializeModuli (r : K → k) :
    (K →₀ ℤ) →+ Divisor k (modularFunctionFieldC k 1) :=
  (charLGeomModuliDictionary k).comp (Finsupp.mapDomain.addMonoidHom r)

omit [Field K] in
@[simp]
theorem specializeModuli_single (r : K → k) (a : K) (n : ℤ) :
    specializeModuli r (Finsupp.single a n)
      = Finsupp.single (specializePlace r a) n := by
  simp only [specializeModuli, AddMonoidHom.coe_comp, Function.comp_apply,
    Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single,
    charLGeomModuliDictionary_single, specializePlace_def]

omit [Field K] in

theorem specializeModuli_eq_mapDomain (r : K → k) (D : K →₀ ℤ) :
    specializeModuli r D = Finsupp.mapDomain (specializePlace r) D := by
  simp only [specializeModuli, AddMonoidHom.coe_comp, Function.comp_apply,
    Finsupp.mapDomain.addMonoidHom_apply, charLGeomModuliDictionary,
    Finsupp.mapDomain.addMonoidHom_apply]
  rw [← Finsupp.mapDomain_comp]
  rfl

theorem specializeModuli_id (D : K →₀ ℤ) :
    specializeModuli (id : K → K) D = charLGeomModuliDictionary K D := by
  simp only [specializeModuli, AddMonoidHom.coe_comp, Function.comp_apply,
    Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_id]

omit [Field K] in
open scoped Classical in

theorem support_specializeModuli_subset (r : K → k) (D : K →₀ ℤ) :
    (specializeModuli r D).support ⊆ D.support.image (specializePlace r) := by
  rw [specializeModuli_eq_mapDomain]
  exact Finsupp.mapDomain_support

end Map

section Degree

variable {K k : Type*} [Field K] [Field k]

omit [Field K] in

theorem degree_specializeModuli_single (r : K → k) (a : K) (n : ℤ) :
    Divisor.degree (specializeModuli r (Finsupp.single a n)) = n := by
  rw [specializeModuli_single, Divisor.degree_single, deg_specializePlace, Nat.cast_one,
    mul_one]

theorem degree_specializeModuli_eq_degree (r : K → k) (D : K →₀ ℤ) :
    Divisor.degree (specializeModuli r D)
      = Divisor.degree (charLGeomModuliDictionary K D) := by
  have h : (Divisor.degree.comp (specializeModuli r) : (K →₀ ℤ) →+ ℤ)
      = Divisor.degree.comp (charLGeomModuliDictionary K) := by
    refine Finsupp.addHom_ext fun a n => ?_
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, specializeModuli_single,
      charLGeomModuliDictionary_single, Divisor.degree_single, deg_specializePlace,
      deg_charLGeomPlaceOfPoint]
  exact DFunLike.congr_fun h D

theorem specializeModuli_mem_degZero (r : K → k) {D : K →₀ ℤ}
    (hD : Divisor.degree (charLGeomModuliDictionary K D) = 0) :
    Divisor.degree (specializeModuli r D) = 0 := by
  rw [degree_specializeModuli_eq_degree, hD]

end Degree

section Galois

variable {K k : Type*} [Field K] [Field k]

omit [Field K] in

theorem specializeModuli_mapDomain (r : K → k) (σ : K → K) (D : K →₀ ℤ) :
    specializeModuli r (Finsupp.mapDomain σ D) = specializeModuli (r ∘ σ) D := by
  rw [specializeModuli_eq_mapDomain, specializeModuli_eq_mapDomain,
    ← Finsupp.mapDomain_comp]
  rfl

omit [Field K] in

theorem specializeModuli_inertia_invariant (r : K → k) (σ : K → K)
    (hσ : ∀ a, r (σ a) = r a) (D : K →₀ ℤ) :
    specializeModuli r (Finsupp.mapDomain σ D) = specializeModuli r D := by
  rw [specializeModuli_mapDomain, show (r ∘ σ) = r from funext hσ]

omit [Field K] in

theorem specializeModuli_intertwines (r : K → k) (σ : K → K) (τ : k → k)
    (h : ∀ a, r (σ a) = τ (r a)) (D : K →₀ ℤ) :
    specializeModuli r (Finsupp.mapDomain σ D)
      = charLGeomModuliDictionary k
          (Finsupp.mapDomain τ (Finsupp.mapDomain r D)) := by
  rw [specializeModuli_mapDomain, show (r ∘ σ) = (τ ∘ r) from funext h,
    ← Finsupp.mapDomain_comp]
  rfl

omit [Field K] in

theorem specializePlace_intertwines (r : K → k) (σ : K → K) (τ : k → k)
    (h : ∀ a, r (σ a) = τ (r a)) (a : K) :
    specializePlace r (σ a) = charLGeomPlaceOfPoint k (τ (r a)) := by
  simp only [specializePlace, h]

end Galois

end ModularCurve

end
