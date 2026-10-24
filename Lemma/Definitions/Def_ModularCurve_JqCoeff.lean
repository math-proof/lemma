import Lemma.Definitions.Def_ModularCurve_X0

set_option autoImplicit false

noncomputable section

open HahnSeries

namespace ModularCurve

section JExpansion

variable (K : Type*) [CommRing K]

def jqModC : LaurentSeries K :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ K (jNum.map (Int.castRingHom K))

def jqNModC (N : ℕ) [NeZero N] : LaurentSeries K := qExpand K N (jqModC K)

@[simp]
theorem jqNModC_one : jqNModC K 1 = jqModC K := qExpand_one_apply _

theorem jqModC_rat : jqModC ℚ = jq := rfl

variable {K} in

theorem map_jqModC {K' : Type*} [CommRing K'] (f : K →+* K') :
    (jqModC K).map f = jqModC K' := by
  have hmul : ∀ x y : LaurentSeries K, (x * y).map f = x.map f * y.map f :=
    fun x y => HahnSeries.map_mul f.toNonUnitalRingHom
  have hsingle : (HahnSeries.single (-1 : ℤ) (1 : K)).map f = HahnSeries.single (-1 : ℤ) 1 := by
    ext g
    rw [HahnSeries.map_coeff, HahnSeries.coeff_single, HahnSeries.coeff_single, apply_ite f,
      map_one, map_zero]
  have hseries : ∀ u : PowerSeries K,
      (HahnSeries.ofPowerSeries ℤ K u).map f = HahnSeries.ofPowerSeries ℤ K' (u.map f) := by
    intro u
    ext k
    rw [HahnSeries.map_coeff]
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map]
    · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _ hk, map_zero]
  rw [jqModC, jqModC, hmul, hsingle, hseries,
    show (jNum.map (Int.castRingHom K)).map f = jNum.map (Int.castRingHom K') from by
      rw [show PowerSeries.map f (PowerSeries.map (Int.castRingHom K) jNum)
            = PowerSeries.map (f.comp (Int.castRingHom K)) jNum from
          (congrFun (congrArg DFunLike.coe (PowerSeries.map_comp (Int.castRingHom K) f)) jNum).symm,
        RingHom.ext_int (f.comp (Int.castRingHom K)) (Int.castRingHom K')]]

theorem jqModC_eq_map_intCast : jqModC K = (jqModC ℤ).map (Int.castRingHom K) :=
  (map_jqModC (Int.castRingHom K)).symm

end JExpansion

section FunctionField

variable (K : Type*) [Field K]

def modularFunctionFieldC (N : ℕ) [NeZero N] :
    IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K {jqModC K, jqNModC K N}

theorem jqModC_mem (N : ℕ) [NeZero N] : jqModC K ∈ modularFunctionFieldC K N :=
  IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)

theorem jqNModC_mem (N : ℕ) [NeZero N] : jqNModC K N ∈ modularFunctionFieldC K N :=
  IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)

theorem modularFunctionFieldC_rat (N : ℕ) [NeZero N] :
    modularFunctionFieldC ℚ N = modularFunctionField N := rfl

theorem modularFunctionFieldC_one :
    modularFunctionFieldC K 1 = IntermediateField.adjoin K {jqModC K} := by
  unfold modularFunctionFieldC
  rw [jqNModC_one, Set.pair_eq_singleton]

end FunctionField

end ModularCurve

end
