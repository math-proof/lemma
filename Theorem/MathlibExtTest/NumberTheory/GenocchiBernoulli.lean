/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GenocchiBernoulli.lean -/
module

public import Theorem.Nat.GenocchiBernoulli
public import Mathlib.Tactic.NormNum

public section

namespace MetaMathlibExtTest

example : MetaMathlibExt.genocchiNumber 1 = 1 := by
  rw [MetaMathlibExt.genocchiNumber_eq_bernoulli, bernoulli_one]
  norm_num

example (n : ℕ) : MetaMathlibExt.genocchiNumberViaBernoulli n = MetaMathlibExt.genocchiNumber n :=
  MetaMathlibExt.genocchiNumberViaBernoulli_eq_genocchiNumber n

end MetaMathlibExtTest
