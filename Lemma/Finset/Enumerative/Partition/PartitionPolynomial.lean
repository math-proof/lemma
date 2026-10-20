import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.Partition.PartitionPolynomial
open MetaMathlibExt


/--
[coeff_partitionPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PartitionPolynomial.lean)
-/
@[path]
private lemma coeff_partitionPolynomial_eq
  {n : ℕ}
  {lam : Nat.Partition n}
  {j : ℕ} :
-- imply
  (partitionPolynomial lam).coeff j = Multiset.count j lam.parts := by
-- proof
  apply MetaMathlibExt.coeff_partitionPolynomial lam j

/--
[eval_partitionPolynomial_at_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PartitionPolynomial.lean)
-/
@[path]
private lemma eval_partitionPolynomial_at_one_eq
  {n : ℕ}
  {lam : Nat.Partition n} :
-- imply
  (partitionPolynomial lam).eval 1 = lam.parts.card := by
-- proof
  apply MetaMathlibExt.eval_partitionPolynomial_at_one lam


-- created on 2026-10-20
