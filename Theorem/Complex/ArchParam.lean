module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Inductive.LanglandsTunnell_RealArchParam
public import Structure.LanglandsTunnell_ArchParam

public noncomputable section

noncomputable section

namespace LanglandsTunnell

open Complex


@[simp] public theorem signShift_zero : signShift 0 = 0 := by simp [signShift]


@[simp] public theorem signShift_one : signShift 1 = 1 := by simp [signShift]

namespace RealArchParam


@[simp] public theorem twist_zero (P : RealArchParam) : P.twist 0 0 = P := by
  cases P <;> simp [twist]


public theorem twist_twist (P : RealArchParam) (u u' : ℂ) (a a' : ZMod 2) :
    (P.twist u a).twist u' a' = P.twist (u + u') (a + a') := by
  cases P <;> simp [twist, add_assoc]


@[simp] public theorem dual_dual (P : RealArchParam) : P.dual.dual = P := by
  cases P <;> simp [dual]


public theorem gammaC_twist (P : RealArchParam) (u : ℂ) (a : ZMod 2) :
    (P.twist u a).gammaC = P.gammaC.map (· + u) := by
  cases P <;> simp [twist, gammaC, add_right_comm]


public theorem gammaR_twist_zero (P : RealArchParam) (u : ℂ) :
    (P.twist u 0).gammaR = P.gammaR.map (· + u) := by
  cases P <;> simp [twist, gammaR, add_right_comm]

end RealArchParam

namespace ComplexArchParam


@[simp] public theorem twist_zero (P : ComplexArchParam) : P.twist 0 0 = P := by
  simp [twist]


public theorem twist_twist (P : ComplexArchParam) (u u' : ℂ) (k k' : ℤ) :
    (P.twist u k).twist u' k' = P.twist (u + u') (k + k') := by
  simp [twist, add_assoc]


@[simp] public theorem dual_dual (P : ComplexArchParam) : P.dual.dual = P := by
  simp [dual]


public theorem gammaC_dual (P : ComplexArchParam) :
    P.dual.gammaC = {-P.u₁ + (P.k₁.natAbs : ℂ) / 2, -P.u₂ + (P.k₂.natAbs : ℂ) / 2} := by
  simp [dual, gammaC]


public theorem gammaC_twist_zero (P : ComplexArchParam) (u : ℂ) :
    (P.twist u 0).gammaC = P.gammaC.map (· + u) := by
  simp [twist, gammaC, add_right_comm]

end ComplexArchParam


public theorem RealArchParam.gammaR_oddArtin : RealArchParam.oddArtin.gammaR = {0, 1} := by
  simp [oddArtin, gammaR]


public theorem ComplexArchParam.gammaC_trivialArtin : ComplexArchParam.trivialArtin.gammaC = {0, 0} := by
  simp [trivialArtin, gammaC]


public theorem RealArchParam.archFactor_oddArtin (s : ℂ) :
    RealArchParam.oddArtin.archFactor s = Gammaℂ s := by
  simp [oddArtin, archFactor, gammaR, gammaC, Gammaℝ_mul_Gammaℝ_add_one]


public theorem ComplexArchParam.archFactor_trivialArtin (s : ℂ) :
    ComplexArchParam.trivialArtin.archFactor s = Gammaℂ s * Gammaℂ s := by
  simp [trivialArtin, archFactor, gammaC]

end LanglandsTunnell

end
