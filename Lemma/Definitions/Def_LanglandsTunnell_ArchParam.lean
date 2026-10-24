import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

noncomputable section

namespace LanglandsTunnell

open Complex

inductive RealArchParam where

  | principal (u₁ : ℂ) (a₁ : ZMod 2) (u₂ : ℂ) (a₂ : ZMod 2) : RealArchParam

  | discrete (u : ℂ) (k : ℕ) (hk : 1 ≤ k) : RealArchParam

@[ext]
structure ComplexArchParam where

  u₁ : ℂ

  k₁ : ℤ

  u₂ : ℂ

  k₂ : ℤ

def signShift (a : ZMod 2) : ℂ := if a = 0 then 0 else 1

@[simp] theorem signShift_zero : signShift 0 = 0 := by simp [signShift]

@[simp] theorem signShift_one : signShift 1 = 1 := by simp [signShift]

namespace RealArchParam

def gammaR : RealArchParam → Multiset ℂ
  | principal u₁ a₁ u₂ a₂ => {u₁ + signShift a₁, u₂ + signShift a₂}
  | discrete _ _ _ => 0

def gammaC : RealArchParam → Multiset ℂ
  | principal _ _ _ _ => 0
  | discrete u k _ => {u + (k : ℂ) / 2}

def archFactor (P : RealArchParam) (s : ℂ) : ℂ :=
  (P.gammaR.map fun μ => Gammaℝ (s + μ)).prod * (P.gammaC.map fun ν => Gammaℂ (s + ν)).prod

def twist : RealArchParam → ℂ → ZMod 2 → RealArchParam
  | principal u₁ a₁ u₂ a₂, u, a => principal (u₁ + u) (a₁ + a) (u₂ + u) (a₂ + a)
  | discrete u₀ k hk, u, _ => discrete (u₀ + u) k hk

def dual : RealArchParam → RealArchParam
  | principal u₁ a₁ u₂ a₂ => principal (-u₁) a₁ (-u₂) a₂
  | discrete u k hk => discrete (-u) k hk

def centralExponent : RealArchParam → ℂ
  | principal u₁ _ u₂ _ => u₁ + u₂
  | discrete u _ _ => 2 * u

def centralSign : RealArchParam → ZMod 2
  | principal _ a₁ _ a₂ => a₁ + a₂
  | discrete _ k _ => (k : ZMod 2) + 1

@[simp] theorem twist_zero (P : RealArchParam) : P.twist 0 0 = P := by
  cases P <;> simp [twist]

theorem twist_twist (P : RealArchParam) (u u' : ℂ) (a a' : ZMod 2) :
    (P.twist u a).twist u' a' = P.twist (u + u') (a + a') := by
  cases P <;> simp [twist, add_assoc]

@[simp] theorem dual_dual (P : RealArchParam) : P.dual.dual = P := by
  cases P <;> simp [dual]

theorem gammaC_twist (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    (P.twist u a).gammaC = P.gammaC.map (· + u) := by
  cases P <;> simp [twist, gammaC, add_right_comm]

theorem gammaR_twist_zero (P : RealArchParam) (u : ℂ) :
    (P.twist u 0).gammaR = P.gammaR.map (· + u) := by
  cases P <;> simp [twist, gammaR, add_right_comm]

end RealArchParam

namespace ComplexArchParam

def gammaC (P : ComplexArchParam) : Multiset ℂ :=
  {P.u₁ + (P.k₁.natAbs : ℂ) / 2, P.u₂ + (P.k₂.natAbs : ℂ) / 2}

def archFactor (P : ComplexArchParam) (s : ℂ) : ℂ :=
  (P.gammaC.map fun ν => Gammaℂ (s + ν)).prod

def twist (P : ComplexArchParam) (u : ℂ) (k : ℤ) : ComplexArchParam :=
  ⟨P.u₁ + u, P.k₁ + k, P.u₂ + u, P.k₂ + k⟩

def dual (P : ComplexArchParam) : ComplexArchParam :=
  ⟨-P.u₁, -P.k₁, -P.u₂, -P.k₂⟩

def centralExponent (P : ComplexArchParam) : ℂ := P.u₁ + P.u₂

def centralTwist (P : ComplexArchParam) : ℤ := P.k₁ + P.k₂

@[simp] theorem twist_zero (P : ComplexArchParam) : P.twist 0 0 = P := by
  simp [twist]

theorem twist_twist (P : ComplexArchParam) (u u' : ℂ) (k k' : ℤ) :
    (P.twist u k).twist u' k' = P.twist (u + u') (k + k') := by
  simp [twist, add_assoc]

@[simp] theorem dual_dual (P : ComplexArchParam) : P.dual.dual = P := by
  simp [dual]

theorem gammaC_dual (P : ComplexArchParam) :
    P.dual.gammaC = {-P.u₁ + (P.k₁.natAbs : ℂ) / 2, -P.u₂ + (P.k₂.natAbs : ℂ) / 2} := by
  simp [dual, gammaC]

theorem gammaC_twist_zero (P : ComplexArchParam) (u : ℂ) :
    (P.twist u 0).gammaC = P.gammaC.map (· + u) := by
  simp [twist, gammaC, add_right_comm]

end ComplexArchParam

def RealArchParam.oddArtin : RealArchParam := .principal 0 0 0 1

def ComplexArchParam.trivialArtin : ComplexArchParam := ⟨0, 0, 0, 0⟩

theorem RealArchParam.gammaR_oddArtin : RealArchParam.oddArtin.gammaR = {0, 1} := by
  simp [oddArtin, gammaR]

theorem ComplexArchParam.gammaC_trivialArtin : ComplexArchParam.trivialArtin.gammaC = {0, 0} := by
  simp [trivialArtin, gammaC]

theorem RealArchParam.archFactor_oddArtin (s : ℂ) :
    RealArchParam.oddArtin.archFactor s = Gammaℂ s := by
  simp [oddArtin, archFactor, gammaR, gammaC, Gammaℝ_mul_Gammaℝ_add_one]

theorem ComplexArchParam.archFactor_trivialArtin (s : ℂ) :
    ComplexArchParam.trivialArtin.archFactor s = Gammaℂ s * Gammaℂ s := by
  simp [trivialArtin, archFactor, gammaC]

end LanglandsTunnell

end
