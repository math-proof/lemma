import Lemma.ModularCurve.JqCoeff
import Lemma.ModularCurve.LaurentCoeff
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois
import Mathlib.FieldTheory.Perfect

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IntermediateField HahnSeries

namespace ModularCurve

namespace coeffSemilinearAut

section CoeffMapLemmas

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeffMap_qExpand (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) :
    coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases h : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem coeffMap_jqModC (f : R →+* S) : coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem coeffMap_jqNModC (f : R →+* S) (N : ℕ) [NeZero N] :
    coeffMap f (jqNModC R N) = jqNModC S N := by
  rw [jqNModC, jqNModC, coeffMap_qExpand, coeffMap_jqModC]

end CoeffMapLemmas

end coeffSemilinearAut

section CoeffAut

variable {K : Type*} [Field K] (N : ℕ) [NeZero N]

theorem coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC (τ : K →+* K) {x : LaurentSeries K}
    (hx : x ∈ modularFunctionFieldC K N) :
    coeffMap τ x ∈ modularFunctionFieldC K N := by
  change x ∈ Subfield.closure (Set.range (algebraMap K (LaurentSeries K)) ∪
      {jqModC K, jqNModC K N}) at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | hy
      · rw [coeffMap_algebraMap]
        exact (modularFunctionFieldC K N).algebraMap_mem _
      · rcases hy with rfl | hy
        · rw [coeffSemilinearAut.coeffMap_jqModC]
          exact jqModC_mem K N
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          rw [coeffSemilinearAut.coeffMap_jqNModC]
          exact jqNModC_mem K N
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

def coeffRingAut (τ : K ≃+* K) : modularFunctionFieldC K N ≃+* modularFunctionFieldC K N where
  toFun x := ⟨coeffMap (τ : K →+* K) (x : LaurentSeries K),
    coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC N (τ : K →+* K) x.2⟩
  invFun x := ⟨coeffMap (τ.symm : K →+* K) (x : LaurentSeries K),
    coeffSemilinearAut.coeffMap_mem_modularFunctionFieldC N (τ.symm : K →+* K) x.2⟩
  left_inv x := Subtype.ext <| by
    show coeffMap (τ.symm : K →+* K) (coeffMap (τ : K →+* K) (x : LaurentSeries K))
      = (x : LaurentSeries K)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => τ.symm_apply_apply a) _, coeffMap_id]
  right_inv x := Subtype.ext <| by
    show coeffMap (τ : K →+* K) (coeffMap (τ.symm : K →+* K) (x : LaurentSeries K))
      = (x : LaurentSeries K)
    rw [coeffMap_coeffMap,
      coeffMap_congr (g := RingHom.id K) (RingHom.ext fun a => τ.apply_symm_apply a) _, coeffMap_id]
  map_mul' x y :=
    Subtype.ext (map_mul (coeffMap (τ : K →+* K)) (x : LaurentSeries K) (y : LaurentSeries K))
  map_add' x y :=
    Subtype.ext (map_add (coeffMap (τ : K →+* K)) (x : LaurentSeries K) (y : LaurentSeries K))

@[simp]
theorem coe_coeffRingAut_apply (τ : K ≃+* K) (x : modularFunctionFieldC K N) :
    (coeffRingAut N τ x : LaurentSeries K) = coeffMap (τ : K →+* K) (x : LaurentSeries K) :=
  rfl

theorem coeffRingAut_algebraMap (τ : K ≃+* K) (a : K) :
    coeffRingAut N τ (algebraMap K (modularFunctionFieldC K N) a)
      = algebraMap K (modularFunctionFieldC K N) (τ a) :=
  Subtype.ext (coeffMap_algebraMap (τ : K →+* K) a)

def coeffSemilinearAut (τ : K ≃+* K) : SemilinearAut K (modularFunctionFieldC K N) :=
  ⟨(coeffRingAut N τ, τ), fun a => coeffRingAut_algebraMap N τ a⟩

@[simp]
theorem toRingAut_coeffSemilinearAut (τ : K ≃+* K) :
    SemilinearAut.toRingAut (coeffSemilinearAut N τ) = coeffRingAut N τ := rfl

@[simp]
theorem baseAut_coeffSemilinearAut (τ : K ≃+* K) :
    SemilinearAut.baseAut (coeffSemilinearAut N τ) = τ := rfl

theorem coe_coeffSemilinearAut_smul (τ : K ≃+* K) (x : modularFunctionFieldC K N) :
    ((coeffSemilinearAut N τ • x : modularFunctionFieldC K N) : LaurentSeries K)
      = coeffMap (τ : K →+* K) (x : LaurentSeries K) := rfl

theorem coeffSemilinearAut_smul_jq (τ : K ≃+* K) :
    coeffSemilinearAut N τ • (⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N)
      = ⟨jqModC K, jqModC_mem K N⟩ :=
  Subtype.ext (coeffSemilinearAut.coeffMap_jqModC (τ : K →+* K))

theorem coeffSemilinearAut_smul_jqN (τ : K ≃+* K) :
    coeffSemilinearAut N τ • (⟨jqNModC K N, jqNModC_mem K N⟩ : modularFunctionFieldC K N)
      = ⟨jqNModC K N, jqNModC_mem K N⟩ :=
  Subtype.ext (coeffSemilinearAut.coeffMap_jqNModC (τ : K →+* K) N)

end CoeffAut

section Frobenius

variable (q : ℕ) (K : Type*) [Field K] [Fact q.Prime] [CharP K q] [PerfectField K]
  (N : ℕ) [NeZero N]

def arithFrobC : SemilinearAut K (modularFunctionFieldC K N) :=
  coeffSemilinearAut N (frobeniusEquiv K q)

@[simp]
theorem baseAut_arithFrobC_apply (a : K) :
    SemilinearAut.baseAut (arithFrobC q K N) a = a ^ q :=
  rfl

theorem arithFrobC_smul_jq :
    arithFrobC q K N • (⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N)
      = ⟨jqModC K, jqModC_mem K N⟩ :=
  coeffSemilinearAut_smul_jq N _

theorem arithFrobC_smul_jqN :
    arithFrobC q K N • (⟨jqNModC K N, jqNModC_mem K N⟩ : modularFunctionFieldC K N)
      = ⟨jqNModC K N, jqNModC_mem K N⟩ :=
  coeffSemilinearAut_smul_jqN N _

end Frobenius

end ModularCurve

end
