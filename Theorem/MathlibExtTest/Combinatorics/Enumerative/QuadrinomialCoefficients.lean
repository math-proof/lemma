/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/QuadrinomialCoefficients.lean -/
module

public import Def.Combinatorics.Enumerative.QuadrinomialCoefficients
public import Theorem.Finset.Enumerative.QuadrinomialCoefficients

public section

namespace MetaMathlibExt

example : quadrinomialCoeff 0 = 1 := by decide

example : quadrinomialCoeff 1 = 1 := by decide

example : quadrinomialCoeff 2 = 3 := by decide

example : quadrinomialCoeff 3 = 10 := by decide

example (n : ℕ) : quadrinomialCoeff n = zhangVSum n 1 1 0 0 0 :=
  quadrinomialCoeff_eq_zhangVSum n

#print axioms zhangVSum
#print axioms quadrinomialCoeff
#print axioms quadrinomialCoeff_eq_zhangVSum

end MetaMathlibExt
