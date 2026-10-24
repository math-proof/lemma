/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/OppermannCyclicNumbers.lean -/


import Mathlib.Tactic
import sympy.atlas.NumberTheory.OppermannCyclicNumbers

namespace MetaMathlibExt

example : IsCyclicNumber 15 := by
  unfold IsCyclicNumber
  decide

example : ¬ IsCyclicNumber 4 := by
  unfold IsCyclicNumber
  decide
example : oppermannCyclicCountLeft 2 = 2 := by decide

end MetaMathlibExt
