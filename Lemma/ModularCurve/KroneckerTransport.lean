import Mathlib
import Lemma.ModularCurve.X0
import Def.ModularCurve_KroneckerTransport

noncomputable section

open PowerSeries HahnSeries IntermediateField

namespace ModularCurve

section LaurentMap

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]


@[simp]
theorem laurentMap_coeff (f : R →+* S) (x : LaurentSeries R) (k : ℤ) :
    (laurentMap f x).coeff k = f (x.coeff k) := rfl

@[simp]
theorem laurentMap_single (f : R →+* S) (k : ℤ) (r : R) :
    laurentMap f (HahnSeries.single k r) = HahnSeries.single k (f r) := by
  ext g
  rw [laurentMap_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single, apply_ite f,
    map_zero]

theorem laurentMap_ofPowerSeries (f : R →+* S) (p : PowerSeries R) :
    laurentMap f (HahnSeries.ofPowerSeries ℤ R p) =
      HahnSeries.ofPowerSeries ℤ S (p.map f) := by
  ext k
  rw [laurentMap_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]

theorem laurentMap_qExpand (f : R →+* S) (N : ℕ) [NeZero N] (x : LaurentSeries R) :
    laurentMap f (qExpand R N x) = qExpand S N (laurentMap f x) := by
  ext k
  rw [laurentMap_coeff]
  by_cases hk : (N : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, qExpand_coeff_mul, laurentMap_coeff]
  · rw [qExpand_coeff_of_not_dvd N x hk, qExpand_coeff_of_not_dvd N _ hk, map_zero]

theorem laurentMap_injective {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (laurentMap f) := by
  intro x y hxy
  ext k
  exact hf (by simpa using congrArg (fun z => z.coeff k) hxy)

theorem laurentMap_laurentMap (f : R →+* S) (g : S →+* T) (x : LaurentSeries R) :
    laurentMap g (laurentMap f x) = laurentMap (g.comp f) x := by
  ext k
  simp

end LaurentMap

section IntegralJ


theorem laurentMap_jqInt : laurentMap (Int.castRingHom ℚ) jqInt = jq := by
  rw [jqInt, map_mul, laurentMap_single, laurentMap_ofPowerSeries, jq, jNumQ, map_one]


theorem laurentMap_jqIntN (N : ℕ) [NeZero N] :
    laurentMap (Int.castRingHom ℚ) (jqIntN N) = jqN N := by
  rw [jqIntN, laurentMap_qExpand, laurentMap_jqInt, jqN]

theorem coeff_jqInt_cast (k : ℤ) : ((jqInt.coeff k : ℤ) : ℚ) = jq.coeff k := by
  rw [← laurentMap_jqInt, laurentMap_coeff]
  rfl

theorem coeff_jqInt_neg_one : jqInt.coeff (-1 : ℤ) = 1 :=
  Int.cast_injective (α := ℚ) (by rw [coeff_jqInt_cast, coeff_jq_neg_one, Int.cast_one])

theorem coeff_jqInt_of_lt {k : ℤ} (hk : k < -1) : jqInt.coeff k = 0 :=
  Int.cast_injective (α := ℚ) (by rw [coeff_jqInt_cast, coeff_jq_of_lt hk, Int.cast_zero])

theorem coeff_jqInt_pow_self (b : ℕ) : (jqInt ^ b).coeff (-(b : ℤ)) = 1 := by
  refine Int.cast_injective (α := ℚ) ?_
  have h : ((jqInt ^ b).coeff (-(b : ℤ)) : ℚ) = (jq ^ b).coeff (-(b : ℤ)) := by
    rw [← laurentMap_jqInt, ← map_pow, laurentMap_coeff]; rfl
  rw [h, coeff_jq_pow_self, Int.cast_one]

theorem coeff_jqInt_pow_of_lt {b : ℕ} {m : ℤ} (hm : m < -(b : ℤ)) :
    (jqInt ^ b).coeff m = 0 := by
  refine Int.cast_injective (α := ℚ) ?_
  have h : ((jqInt ^ b).coeff m : ℚ) = (jq ^ b).coeff m := by
    rw [← laurentMap_jqInt, ← map_pow, laurentMap_coeff]; rfl
  rw [h, coeff_jq_pow_of_lt hm, Int.cast_zero]

end IntegralJ

section ReduceModBivar


@[simp] theorem reduceModBivar_X (ℓ : ℕ) :
    reduceModBivar ℓ Polynomial.X = Polynomial.X := by
  simp [reduceModBivar, Polynomial.coe_mapRingHom]

@[simp] theorem reduceModBivar_C_X (ℓ : ℕ) :
    reduceModBivar ℓ (Polynomial.C Polynomial.X) = Polynomial.C Polynomial.X := by
  simp [reduceModBivar, Polynomial.coe_mapRingHom]

end ReduceModBivar


section IntegralEquation


@[simp]
theorem evalAtJInt_X : evalAtJInt Polynomial.X = jqInt :=
  Polynomial.eval₂_X _ _

theorem laurentMap_comp_evalAtJInt :
    (laurentMap (Int.castRingHom ℚ)).comp evalAtJInt = evalAtJ := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  rw [RingHom.comp_apply, evalAtJInt_X, laurentMap_jqInt, evalAtJ_X]

end IntegralEquation

section ModEquation

variable (ℓ : ℕ)


@[simp]
theorem jqNMod_one : jqNMod ℓ 1 = jqMod ℓ := qExpand_one_apply _

theorem laurentMap_jqIntN_mod (N : ℕ) [NeZero N] :
    laurentMap (Int.castRingHom (ZMod ℓ)) (jqIntN N) = jqNMod ℓ N := by
  rw [jqIntN, laurentMap_qExpand, jqNMod, jqMod]

theorem coeff_jqMod (k : ℤ) : (jqMod ℓ).coeff k = (jqInt.coeff k : ZMod ℓ) := rfl

theorem coeff_jqMod_neg_one : (jqMod ℓ).coeff (-1 : ℤ) = 1 := by
  rw [coeff_jqMod, coeff_jqInt_neg_one, Int.cast_one]

theorem coeff_jqMod_of_lt {k : ℤ} (hk : k < -1) : (jqMod ℓ).coeff k = 0 := by
  rw [coeff_jqMod, coeff_jqInt_of_lt hk, Int.cast_zero]

theorem coeff_jqMod_pow_self (b : ℕ) : ((jqMod ℓ) ^ b).coeff (-(b : ℤ)) = 1 := by
  have h : ((jqMod ℓ) ^ b).coeff (-(b : ℤ)) = ((jqInt ^ b).coeff (-(b : ℤ)) : ZMod ℓ) := by
    rw [jqMod, ← map_pow, laurentMap_coeff]; rfl
  rw [h, coeff_jqInt_pow_self, Int.cast_one]

theorem coeff_jqMod_pow_of_lt {b : ℕ} {m : ℤ} (hm : m < -(b : ℤ)) :
    ((jqMod ℓ) ^ b).coeff m = 0 := by
  have h : ((jqMod ℓ) ^ b).coeff m = ((jqInt ^ b).coeff m : ZMod ℓ) := by
    rw [jqMod, ← map_pow, laurentMap_coeff]; rfl
  rw [h, coeff_jqInt_pow_of_lt hm, Int.cast_zero]


@[simp]
theorem evalAtJMod_X : evalAtJMod ℓ Polynomial.X = jqMod ℓ :=
  Polynomial.eval₂_X _ _

theorem evalAtJMod_comp_map :
    (evalAtJMod ℓ).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) =
      (laurentMap (Int.castRingHom (ZMod ℓ))).comp evalAtJInt := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  rw [RingHom.comp_apply, RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
    evalAtJMod_X, evalAtJInt_X, jqMod]

end ModEquation

section ModFunctionField

variable (ℓ : ℕ) [Fact ℓ.Prime]


theorem jqMod_mem (N : ℕ) [NeZero N] : jqMod ℓ ∈ modularFunctionFieldMod ℓ N :=
  IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)

theorem jqNMod_mem (N : ℕ) [NeZero N] : jqNMod ℓ N ∈ modularFunctionFieldMod ℓ N :=
  IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)

end ModFunctionField

end ModularCurve

end
