module

public import Theorem.HahnSeries.X0
public import Theorem.UpperHalfPlane.EtaQuotient
public import Theorem.PowerSeries.TateFormal
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

public noncomputable section

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

namespace ModularCurve


public theorem shimuraGamma_mem (p : ℕ) (A : SL(2, ℤ)) :
    A ∈ shimuraGamma p ↔
      ((A 1 0 : ZMod p) = 0 ∧ (A 1 1 : ZMod p) ^ sharpIndex p = 1) := by
  rw [shimuraGamma, Subgroup.mem_map]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ.2, hγ⟩
  · rintro ⟨h0, h1⟩
    exact ⟨⟨A, h0⟩, h1, rfl⟩


public theorem shimuraGamma_le_gamma0 (p : ℕ) :
    shimuraGamma p ≤ CongruenceSubgroup.Gamma0 p := by
  intro A hA
  exact ((shimuraGamma_mem p A).mp hA).1


public theorem gamma1_le_shimuraGamma (p : ℕ) :
    CongruenceSubgroup.Gamma1 p ≤ shimuraGamma p := by
  intro A hA
  rw [CongruenceSubgroup.Gamma1_mem] at hA
  rw [shimuraGamma_mem]
  exact ⟨hA.2.2, by rw [hA.2.1, one_pow]⟩


public theorem gamma_le_shimuraGamma (p : ℕ) :
    CongruenceSubgroup.Gamma p ≤ shimuraGamma p := by
  intro A hA
  rw [CongruenceSubgroup.Gamma_mem] at hA
  rw [shimuraGamma_mem]
  exact ⟨hA.2.2.1, by rw [hA.2.2.2, one_pow]⟩


public theorem coeff_shimuraPeriodSeries (p : ℕ) (v : (ZMod p)ˣ) (n : ℕ) :
    PowerSeries.coeff n (shimuraPeriodSeries p v) =
      if n = 0 then shimuraConstant p v
      else 2 * (p : ℚ) *
        ∑ d ∈ n.divisors.filter
          (fun d : ℕ => (d : ZMod p) ^ sharpIndex p = (v : ZMod p) ^ sharpIndex p),
          (d : ℚ) :=
  PowerSeries.coeff_mk n _


public theorem constantCoeff_shimuraPeriodSeries (p : ℕ) (v : (ZMod p)ˣ) :
    PowerSeries.constantCoeff (shimuraPeriodSeries p v) = shimuraConstant p v := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_shimuraPeriodSeries, if_pos rfl]


public theorem shimuraConstant_congr (p : ℕ) {v v' : (ZMod p)ˣ}
    (h : (v : ZMod p) ^ sharpIndex p = (v' : ZMod p) ^ sharpIndex p) :
    shimuraConstant p v = shimuraConstant p v' := by
  have hf : ∀ s : Finset ℕ,
      (s.filter fun d : ℕ => (d : ZMod p) ^ sharpIndex p = (v : ZMod p) ^ sharpIndex p) =
        (s.filter fun d : ℕ =>
          (d : ZMod p) ^ sharpIndex p = (v' : ZMod p) ^ sharpIndex p) :=
    fun s => Finset.filter_congr fun d _ => by rw [h]
  unfold shimuraConstant
  rw [hf]


public theorem shimuraPeriodSeries_congr (p : ℕ) {v v' : (ZMod p)ˣ}
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


public theorem constantCoeff_shimuraGenNum (p : ℕ) (v : (ZMod p)ˣ) :
    PowerSeries.constantCoeff (shimuraGenNum p v) = shimuraConstant p v := by
  have h : PowerSeries.constantCoeff
      ((eisenstein4 * eisenstein6 * dedekindEtaUnitInv).map (Int.castRingHom ℚ)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [map_mul, constantCoeff_eisenstein4, constantCoeff_eisenstein6,
      constantCoeff_dedekindEtaUnitInv]
  rw [shimuraGenNum, map_mul, h, constantCoeff_shimuraPeriodSeries, one_mul]


public theorem shimuraGenSeries_def (p : ℕ) (v : (ZMod p)ˣ) :
    shimuraGenSeries p v =
      HahnSeries.single (-1 : ℤ) (-(1 / 2592) : ℚ) *
        HahnSeries.ofPowerSeries ℤ ℚ
          ((eisenstein4 * eisenstein6 * dedekindEtaUnitInv).map (Int.castRingHom ℚ) *
            shimuraPeriodSeries p v) :=
  rfl


public theorem shimuraGenSeries_congr (p : ℕ) {v v' : (ZMod p)ˣ}
    (h : (v : ZMod p) ^ sharpIndex p = (v' : ZMod p) ^ sharpIndex p) :
    shimuraGenSeries p v = shimuraGenSeries p v' := by
  rw [shimuraGenSeries, shimuraGenSeries, shimuraGenNum, shimuraGenNum,
    shimuraPeriodSeries_congr p h]


public theorem coeff_neg_one_shimuraGenSeries (p : ℕ) (v : (ZMod p)ˣ) :
    (shimuraGenSeries p v).coeff (-1 : ℤ) = -(1 / 2592 : ℚ) * shimuraConstant p v := by
  rw [shimuraGenSeries, HahnSeries.coeff_single_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_shimuraGenNum]

section FunctionField

variable (p : ℕ)


public theorem modularFunctionFieldFull_le_shimuraFunctionField :
    modularFunctionFieldFull p ≤ shimuraFunctionField p := by
  rw [modularFunctionFieldFull, shimuraFunctionField]
  exact IntermediateField.adjoin.mono ℚ _ _ Set.subset_union_left


public theorem shimuraGenSeries_mem_shimuraFunctionField (v : (ZMod p)ˣ) :
    shimuraGenSeries p v ∈ shimuraFunctionField p :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_union_right _ ⟨v, rfl⟩)

