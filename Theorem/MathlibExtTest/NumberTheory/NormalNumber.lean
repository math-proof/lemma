/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NormalNumber.lean -/
module

public import Def.NumberTheory.NormalNumber
public import Theorem.Nat.NormalNumber
open MetaMathlibExt.NormalNumber

public section

example (b n : ℕ) (x : ℝ) : digitSeq b x n = ⌊(b : ℝ) ^ (n + 1) * Int.fract x⌋₊ % b :=
  rfl

#check IsNormalInBase.isSimplyNormalInBase
#check IsAbsolutelyNormal

#print axioms digitSeq
#print axioms IsSimplyNormalInBase
#print axioms IsNormalInBase
#print axioms IsAbsolutelyNormal

