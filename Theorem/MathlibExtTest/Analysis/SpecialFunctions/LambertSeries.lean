/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/LambertSeries.lean -/
module

public import Mathlib.Tactic.NormNum
public import Def.Analysis.SpecialFunctions.LambertSeries
public import Def.MathlibExtTest.Analysis.SpecialFunctions.LambertSeries

public section

namespace MetaMathlibExt

example (k : ℕ) : lambertSeriesSummand zeroInUnitDisk k = 0 := by
  simp [lambertSeriesSummand, zeroInUnitDisk]

example : lambertSeries zeroInUnitDisk = 0 := by
  simp [lambertSeries, lambertSeriesSummand, zeroInUnitDisk]

example (k : ℕ) : lambertGSummand zeroInUnitDisk k = 0 := by
  simp [lambertGSummand, zeroInUnitDisk]

end MetaMathlibExt
