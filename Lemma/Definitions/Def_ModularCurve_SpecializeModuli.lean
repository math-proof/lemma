import Mathlib
import Lemma.Definitions.Def_ModularCurve_JqCoeff
import Lemma.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Theorems.Thm_ModularCurve_transcendental_jqModC

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section Transcendence

variable (K : Type*) [Field K]

def ratFuncEquivCharLOneC : RatFunc K ≃ₐ[K] (modularFunctionFieldC K 1) :=
  (RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K)).trans
    (IntermediateField.equivOfEq (modularFunctionFieldC_one K).symm)

end Transcendence

section Jacobian

variable (K : Type*) [Field K]

abbrev charLJacobian (N : ℕ) [NeZero N] : Type _ :=
  Pic0 K (modularFunctionFieldC K N)

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
