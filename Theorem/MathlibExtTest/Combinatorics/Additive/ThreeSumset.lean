/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Additive/ThreeSumset.lean -/
module

public import Def.Combinatorics.Additive.ThreeSumset.Part3
public import Theorem.Finset.Additive.ThreeSumset
open scoped Pointwise

public section

namespace MetaMathlibExt

example (A B C : Finset (ZMod 5)) :
    ((A + B + C).card : ℕ) ^ 2 ≤ (A + B).card * (B + C).card * (C + A).card :=
  gyarmatiMatolcsiRuzsa_three_sumset_zmod 5 (by decide) (by decide) A B C

end MetaMathlibExt
