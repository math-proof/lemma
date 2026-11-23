/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/SternSequence.lean -/
module

public import Def.NumberTheory.SternSequence
public import Theorem.Nat.SternSequence

public section

namespace MetaMathlibExt

example : sternSequence 0 = 0 := stern_zero

example : sternSequence 1 = 1 := stern_one

example : sternSequence 2 = 1 := by
  simpa [stern_one] using stern_even 1 (by decide)

example : sternSequence 3 = 2 := by
  have htwo : sternSequence 2 = 1 := by
    simpa [stern_one] using stern_even 1 (by decide)
  simpa [stern_one, htwo] using stern_odd 1 (by decide)

example : sternSequence (2 * 1) = sternSequence 1 :=
  stern_even 1 (by decide)

example : sternSequence (2 * 1 + 1) = sternSequence 1 + sternSequence (1 + 1) :=
  stern_odd 1 (by decide)

end MetaMathlibExt
