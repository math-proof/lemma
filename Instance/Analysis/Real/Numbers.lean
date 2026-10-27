import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Basic.ENNReal.Real
import Notation.Analysis.Real.Numbers
export Complex (I)


namespace ENNReal.ToRealCoe

noncomputable scoped instance : CoeTC ENNReal ℝ := ⟨ENNReal.toReal⟩

end ENNReal.ToRealCoe
