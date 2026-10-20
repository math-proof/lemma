/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PartitionPolynomial.lean -/

import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Combinatorics.Enumerative.Partition.Basic

namespace MetaMathlibExt

/-- Unnormalized partition polynomial `f_λ` (concept
`jis_term_a06e44e4f62cf3639dfdaa73`, source
`jis_source_4a49f53a6c92c67501cd5ea5`). -/
noncomputable def partitionPolynomial {n : ℕ} (lam : Nat.Partition n) :
    Polynomial ℕ :=
  (lam.parts.map fun a => (Polynomial.X : Polynomial ℕ) ^ a).sum

/-- Coefficients recover part multiplicities (concept
`jis_term_a06e44e4f62cf3639dfdaa73`, source
`jis_source_4a49f53a6c92c67501cd5ea5`). -/
theorem coeff_partitionPolynomial {n : ℕ} (lam : Nat.Partition n) (j : ℕ) :
    (partitionPolynomial lam).coeff j = Multiset.count j lam.parts := by
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

/-- Evaluation at one recovers the number of parts (concept
`jis_term_a06e44e4f62cf3639dfdaa73`, source
`jis_source_4a49f53a6c92c67501cd5ea5`). -/
theorem eval_partitionPolynomial_at_one {n : ℕ} (lam : Nat.Partition n) :
    (partitionPolynomial lam).eval 1 = lam.parts.card := by
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
