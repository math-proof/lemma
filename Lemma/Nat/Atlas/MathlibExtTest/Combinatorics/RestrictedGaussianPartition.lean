import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Combinatorics.RestrictedGaussianPartition
open MetaMathlibExt


/--
[isPrimePowTwo](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/RestrictedGaussianPartition.lean)
-/
@[path]
lemma isPrimePowTwo
-- imply
  IsPrimePow 2 := by
-- proof
  decide

/--
[notPrimePowOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/RestrictedGaussianPartition.lean)
-/
@[path]
lemma notPrimePowOne
-- imply
  ¬ IsPrimePow 1 := by
-- proof
  decide


-- created on 2026-10-23
