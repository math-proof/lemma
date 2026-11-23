module

public import Theorem.HahnSeries.X0
public import Theorem.UpperHalfPlane.EtaQuotient
public import Theorem.PowerSeries.TateFormal
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

@[expose] public section

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

def shimuraGenNum (p : ℕ) (v : (ZMod p)ˣ) : PowerSeries ℚ :=
  (eisenstein4 * eisenstein6 * dedekindEtaUnitInv).map (Int.castRingHom ℚ) *
    shimuraPeriodSeries p v

def shimuraGenSeries (p : ℕ) (v : (ZMod p)ˣ) : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) (-(1 / 2592) : ℚ) *
    HahnSeries.ofPowerSeries ℤ ℚ (shimuraGenNum p v)

section FunctionField

variable (p : ℕ)

def shimuraFunctionField : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ (divisorExpansions p ∪ Set.range (shimuraGenSeries p))

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

end
