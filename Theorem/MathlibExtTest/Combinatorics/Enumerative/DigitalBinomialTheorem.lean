/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/DigitalBinomialTheorem.lean -/
module

public import Def.Combinatorics.Enumerative.DigitalBinomialTheorem
public import Theorem.Finset.Enumerative.DigitalBinomialTheorem

public section

namespace MetaMathlibExt

example : (List.range 8).map binDigitSum = [0, 1, 1, 2, 1, 2, 2, 3] := by decide

example : binDigitSum 0 = 0 := by simp

example : binDigitSum 1 = 1 := by simp

example (k : ℕ) : binDigitSum (2 * (2 * k + 1)) = binDigitSum k + 1 := by simp

end MetaMathlibExt
