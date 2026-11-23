module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Structure.LanglandsTunnell_HonestLDatum

public noncomputable section

noncomputable section

open Complex Polynomial

namespace LanglandsTunnell


namespace LDatum

variable {ι : Type*} (D : LDatum ι)


@[simp] public theorem badFactor_zero (s : ℂ) : badFactor 0 s = 1 := by
  simp [badFactor]


public theorem isBadData_zero : IsBadData 0 := fun _ h => (Multiset.notMem_zero _ h).elim


public theorem archFactor_of_gammaC_eq_zero (hC : D.gammaC = 0) (s : ℂ) :
    D.archFactor s = (D.gammaR.map fun μ => Gammaℝ (s + μ)).prod := by
  simp [archFactor, hC]

end LDatum

end LanglandsTunnell

end
