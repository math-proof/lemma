/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/OppermannCyclicNumbers.lean -/
module

public import Mathlib.Tactic
public import Def.NumberTheory.OppermannCyclicNumbers

public section

namespace MetaMathlibExt

example : IsCyclicNumber 15 := by
  unfold IsCyclicNumber
  decide

example : ¬ IsCyclicNumber 4 := by
  unfold IsCyclicNumber
  decide

example : oppermannCyclicCountLeft 2 = 2 := by decide

end MetaMathlibExt
