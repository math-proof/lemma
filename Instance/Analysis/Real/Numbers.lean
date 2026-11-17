module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Real.Hyperreal
public import Mathlib.Basic.ENNReal.Real
public import Notation.Analysis.Real.Numbers

@[expose] public section

export Complex (I)


namespace ENNReal.ToRealCoe

noncomputable scoped instance : CoeTC ENNReal ℝ := ⟨ENNReal.toReal⟩

end ENNReal.ToRealCoe
