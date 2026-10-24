import Lemma.Definitions.Def_ModularCurve_X0
import Lemma.Definitions.Def_ModularCurve_EtaQuotient
import Lemma.Definitions.Def_ModularCurve_TateFormal
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace ModularCurve

def shimuraGamma' (p : ℕ) : Subgroup (CongruenceSubgroup.Gamma0 p) where
  carrier := {γ | CongruenceSubgroup.Gamma0Map p γ ^ sharpIndex p = 1}
  one_mem' := by simp only [Set.mem_setOf_eq, map_one, one_pow]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, mul_pow, ha, hb, one_mul]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have h1 : CongruenceSubgroup.Gamma0Map p a * CongruenceSubgroup.Gamma0Map p a⁻¹ = 1 := by
      rw [← map_mul]
      simp
    calc CongruenceSubgroup.Gamma0Map p a⁻¹ ^ sharpIndex p
        = CongruenceSubgroup.Gamma0Map p a ^ sharpIndex p *
            CongruenceSubgroup.Gamma0Map p a⁻¹ ^ sharpIndex p := by rw [ha, one_mul]
      _ = (CongruenceSubgroup.Gamma0Map p a * CongruenceSubgroup.Gamma0Map p a⁻¹) ^
            sharpIndex p := (mul_pow _ _ _).symm
      _ = 1 := by rw [h1, one_pow]

def shimuraGamma (p : ℕ) : Subgroup SL(2, ℤ) :=
  Subgroup.map (CongruenceSubgroup.Gamma0 p).subtype (shimuraGamma' p)

theorem shimuraGamma_mem (p : ℕ) (A : SL(2, ℤ)) :
    A ∈ shimuraGamma p ↔
      ((A 1 0 : ZMod p) = 0 ∧ (A 1 1 : ZMod p) ^ sharpIndex p = 1) := by
  rw [shimuraGamma, Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ.2, hγ⟩
  · rintro ⟨h0, h1⟩
    exact ⟨⟨A, h0⟩, h1, rfl⟩

theorem shimuraGamma_le_gamma0 (p : ℕ) :
    shimuraGamma p ≤ CongruenceSubgroup.Gamma0 p := by
  intro A hA
  exact ((shimuraGamma_mem p A).mp hA).1

theorem gamma1_le_shimuraGamma (p : ℕ) :
    CongruenceSubgroup.Gamma1 p ≤ shimuraGamma p := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  rw [shimuraGamma_mem]
  exact ⟨hA.2.2, by rw [hA.2.1, one_pow]⟩

theorem gamma_le_shimuraGamma (p : ℕ) :
    CongruenceSubgroup.Gamma p ≤ shimuraGamma p := by
  intro A hA
  rw [CongruenceSubgroup.Gamma_mem] at hA
  rw [shimuraGamma_mem]
  exact ⟨hA.2.2.1, by rw [hA.2.2.2, one_pow]⟩

def shimuraConstant (p : ℕ) (v : (ZMod p)ˣ) : ℚ :=
  -((sharpIndex p : ℚ) * (p : ℚ) ^ 2) / 12 +
    (∑ h ∈ (Finset.Ico 1 p).filter
        (fun h : ℕ => (h : ZMod p) ^ sharpIndex p = (v : ZMod p) ^ sharpIndex p),
      (h : ℚ) * ((p : ℚ) - (h : ℚ))) / 2

def shimuraPeriodSeries (p : ℕ) (v : (ZMod p)ˣ) : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if n = 0 then shimuraConstant p v
    else 2 * (p : ℚ) *
      ∑ d ∈ n.divisors.filter
        (fun d : ℕ => (d : ZMod p) ^ sharpIndex p = (v : ZMod p) ^ sharpIndex p), (d : ℚ)

theorem coeff_shimuraPeriodSeries (p : ℕ) (v : (ZMod p)ˣ) (n : ℕ) :
    PowerSeries.coeff n (shimuraPeriodSeries p v) =
      if n = 0 then shimuraConstant p v
      else 2 * (p : ℚ) *
        ∑ d ∈ n.divisors.filter
          (fun d : ℕ => (d : ZMod p) ^ sharpIndex p = (v : ZMod p) ^ sharpIndex p),
          (d : ℚ) :=
  PowerSeries.coeff_mk n _

theorem constantCoeff_shimuraPeriodSeries (p : ℕ) (v : (ZMod p)ˣ) :
    PowerSeries.constantCoeff (shimuraPeriodSeries p v) = shimuraConstant p v := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_shimuraPeriodSeries, if_pos rfl]

theorem shimuraConstant_congr (p : ℕ) {v v' : (ZMod p)ˣ}
    (h : (v : ZMod p) ^ sharpIndex p = (v' : ZMod p) ^ sharpIndex p) :
    shimuraConstant p v = shimuraConstant p v' := by
  have hf : ∀ s : Finset ℕ,
      (s.filter fun d : ℕ => (d : ZMod p) ^ sharpIndex p = (v : ZMod p) ^ sharpIndex p) =
        (s.filter fun d : ℕ =>
          (d : ZMod p) ^ sharpIndex p = (v' : ZMod p) ^ sharpIndex p) :=
    fun s => Finset.filter_congr fun d _ => by rw [h]
  unfold shimuraConstant
  rw [hf]

theorem shimuraPeriodSeries_congr (p : ℕ) {v v' : (ZMod p)ˣ}
    (h : (v : ZMod p) ^ sharpIndex p = (v' : ZMod p) ^ sharpIndex p) :
    shimuraPeriodSeries p v = shimuraPeriodSeries p v' := by
  have hf : ∀ s : Finset ℕ,
      (s.filter fun d : ℕ => (d : ZMod p) ^ sharpIndex p = (v : ZMod p) ^ sharpIndex p) =
        (s.filter fun d : ℕ =>
          (d : ZMod p) ^ sharpIndex p = (v' : ZMod p) ^ sharpIndex p) :=
    fun s => Finset.filter_congr fun d _ => by rw [h]
  unfold shimuraPeriodSeries
  rw [shimuraConstant_congr p h]
  congr 1
  funext n
  by_cases hn : n = 0
  · rw [if_pos hn, if_pos hn]
  · rw [if_neg hn, if_neg hn, hf]

def shimuraGenNum (p : ℕ) (v : (ZMod p)ˣ) : PowerSeries ℚ :=
  (eisenstein4 * eisenstein6 * dedekindEtaUnitInv).map (Int.castRingHom ℚ) *
    shimuraPeriodSeries p v

theorem constantCoeff_shimuraGenNum (p : ℕ) (v : (ZMod p)ˣ) :
    PowerSeries.constantCoeff (shimuraGenNum p v) = shimuraConstant p v := by
  have h : PowerSeries.constantCoeff
      ((eisenstein4 * eisenstein6 * dedekindEtaUnitInv).map (Int.castRingHom ℚ)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [map_mul, constantCoeff_eisenstein4, constantCoeff_eisenstein6,
      constantCoeff_dedekindEtaUnitInv]
  rw [shimuraGenNum, map_mul, h, constantCoeff_shimuraPeriodSeries, one_mul]

def shimuraGenSeries (p : ℕ) (v : (ZMod p)ˣ) : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) (-(1 / 2592) : ℚ) *
    HahnSeries.ofPowerSeries ℤ ℚ (shimuraGenNum p v)

theorem shimuraGenSeries_def (p : ℕ) (v : (ZMod p)ˣ) :
    shimuraGenSeries p v =
      HahnSeries.single (-1 : ℤ) (-(1 / 2592) : ℚ) *
        HahnSeries.ofPowerSeries ℤ ℚ
          ((eisenstein4 * eisenstein6 * dedekindEtaUnitInv).map (Int.castRingHom ℚ) *
            shimuraPeriodSeries p v) :=
  rfl

theorem shimuraGenSeries_congr (p : ℕ) {v v' : (ZMod p)ˣ}
    (h : (v : ZMod p) ^ sharpIndex p = (v' : ZMod p) ^ sharpIndex p) :
    shimuraGenSeries p v = shimuraGenSeries p v' := by
  rw [shimuraGenSeries, shimuraGenSeries, shimuraGenNum, shimuraGenNum,
    shimuraPeriodSeries_congr p h]

theorem coeff_neg_one_shimuraGenSeries (p : ℕ) (v : (ZMod p)ˣ) :
    (shimuraGenSeries p v).coeff (-1 : ℤ) = -(1 / 2592 : ℚ) * shimuraConstant p v := by
  rw [shimuraGenSeries, HahnSeries.coeff_single_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_shimuraGenNum]

section FunctionField

variable (p : ℕ)

def shimuraFunctionField : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ (divisorExpansions p ∪ Set.range (shimuraGenSeries p))

theorem modularFunctionFieldFull_le_shimuraFunctionField :
    modularFunctionFieldFull p ≤ shimuraFunctionField p := by
  rw [modularFunctionFieldFull, shimuraFunctionField]
  exact IntermediateField.adjoin.mono ℚ _ _ Set.subset_union_left

theorem shimuraGenSeries_mem_shimuraFunctionField (v : (ZMod p)ˣ) :
    shimuraGenSeries p v ∈ shimuraFunctionField p :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_union_right _ ⟨v, rfl⟩)

def IsShimuraDeck
    (δ : (ZMod p)ˣ →* (shimuraFunctionField p ≃ₐ[ℚ] shimuraFunctionField p)) : Prop :=
  (∀ (d : (ZMod p)ˣ) (x : shimuraFunctionField p),
      (x : LaurentSeries ℚ) ∈ modularFunctionFieldFull p → δ d x = x) ∧
  (∀ d v : (ZMod p)ˣ,
      (δ d ⟨shimuraGenSeries p v, shimuraGenSeries_mem_shimuraFunctionField p v⟩ :
        LaurentSeries ℚ) = shimuraGenSeries p (v * d))

end FunctionField

end ModularCurve

end
