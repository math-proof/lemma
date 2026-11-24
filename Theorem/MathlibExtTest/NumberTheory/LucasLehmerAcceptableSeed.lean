module
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Theorem.NumberTheory.LucasLehmerAcceptableSeed.Part9
public import Theorem.Nat.LucasLehmerAcceptableSeed
open MetaMathlibExt


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LucasLehmerAcceptableSeed.lean -/
-- The Jacobi conditions for seed 4 certify the Mersenne prime 31.

example : Nat.Prime (mersenne 5) := by
  apply (acceptableSeed_of_jacobi 5 (by decide) (by norm_num) 4 (by
    norm_num [mersenne])).2
  norm_num [mersenne, Function.iterate_succ_apply']

