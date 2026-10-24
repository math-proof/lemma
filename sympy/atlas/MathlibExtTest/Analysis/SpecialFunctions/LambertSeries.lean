/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/LambertSeries.lean -/


import Mathlib.Tactic.NormNum
import sympy.atlas.Analysis.SpecialFunctions.LambertSeries

namespace MetaMathlibExt

private noncomputable def zeroInUnitDisk : {q : ℂ // ‖q‖ < 1} :=
  ⟨0, by norm_num⟩

example (k : ℕ) : lambertSeriesSummand zeroInUnitDisk k = 0 := by
  simp [lambertSeriesSummand, zeroInUnitDisk]

example : lambertSeries zeroInUnitDisk = 0 := by
  simp [lambertSeries, lambertSeriesSummand, zeroInUnitDisk]

example (k : ℕ) : lambertGSummand zeroInUnitDisk k = 0 := by
  simp [lambertGSummand, zeroInUnitDisk]

end MetaMathlibExt
