import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.Partition.PartitionPolynomial
open MetaMathlibExt


namespace MetaMathlibExt

/--
[coeff_partitionPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PartitionPolynomial.lean)
-/
@[path]
lemma coeff_partitionPolynomial
  {n : ℕ}
  {lam : Nat.Partition n}
  {j : ℕ} :
-- imply
  (partitionPolynomial lam).coeff j = Multiset.count j lam.parts := by
-- proof
  have key : ∀ t : Multiset ℕ,
    ((Multiset.map (fun b => (Polynomial.X : Polynomial ℕ) ^ b) t).sum).coeff j =
      Multiset.count j t := by
    intro t
    induction t using Multiset.induction with
    | empty => simp
    | cons b t ih =>
      simp [Multiset.map_cons, Multiset.sum_cons, Polynomial.coeff_add,
        Polynomial.coeff_X_pow, Multiset.count_cons, ih, add_comm]
  simpa [partitionPolynomial] using key lam.parts

end MetaMathlibExt

namespace MetaMathlibExt

/--
[eval_partitionPolynomial_at_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PartitionPolynomial.lean)
-/
@[path]
lemma eval_partitionPolynomial_at_one
  {n : ℕ}
  {lam : Nat.Partition n} :
-- imply
  (partitionPolynomial lam).eval 1 = lam.parts.card := by
-- proof
  have key : ∀ t : Multiset ℕ,
    ((Multiset.map (fun b => (Polynomial.X : Polynomial ℕ) ^ b) t).sum).eval 1 =
      Multiset.card t := by
    intro t
    induction t using Multiset.induction with
    | empty => simp
    | cons b t ih =>
      simp [Multiset.map_cons, Multiset.sum_cons, Polynomial.eval_add,
        Polynomial.eval_pow, Polynomial.eval_X, Multiset.card_cons, ih, add_comm]
  simpa [partitionPolynomial] using key lam.parts

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-26
