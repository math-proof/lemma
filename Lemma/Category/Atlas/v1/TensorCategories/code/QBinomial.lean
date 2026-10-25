import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.TensorCategories.code.QBinomial.Part2


/--
[qBinomial_zero_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
lemma qBinomial_zero_right
  [Field k]
  {q : k}
  {n : ℕ} :
-- imply
  qBinomial q n 0 = 1 := by
-- proof
  cases n <;> simp [qBinomial]

/--
[qBinomial_eq_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma qBinomial_eq_zero_of_lt_eq
  [Field k]
  {q : k}
  {n m : ℕ}
-- given
  (h : n < m) :
-- imply
  qBinomial q n m = 0 := by
-- proof
  apply qBinomial_eq_zero_of_lt q n m h

/--
[qBinomial_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma qBinomial_self_eq
  [Field k]
  {q : k} :
-- imply
  ∀ n : ℕ, qBinomial q n n = 1 := by
-- proof
  apply qBinomial_self q

/--
[qFallingFact_succ_last](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma qFallingFact_succ_last_eq
  [Field k]
  {q : k}
  {n m : ℕ} :
-- imply
  qFallingFact q n (m + 1) = qFallingFact q n m * (q ^ (n - m) - 1) := by
-- proof
  apply qFallingFact_succ_last q n m

/--
[qFactorial_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma qFactorial_succ_eq
  [Field k]
  {q : k}
  {m : ℕ} :
-- imply
  qFactorial q (m + 1) = qFactorial q m * (q ^ (m + 1) - 1) := by
-- proof
  apply qFactorial_succ q m

/--
[qFallingFact_succ_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma qFallingFact_succ_succ_eq
  [Field k]
  {q : k}
  {n m : ℕ} :
-- imply
  qFallingFact q (n + 1) (m + 1) = qFallingFact q n m * (q ^ (n + 1) - 1) := by
-- proof
  apply qFallingFact_succ_succ q n m

/--
[q_product_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma q_product_identity_eq
  [Field k]
  {q : k}
  {n m : ℕ}
-- given
  (hm : m ≤ n) :
-- imply
  q ^ (m + 1) * (q ^ (n - m) - 1) + (q ^ (m + 1) - 1) = q ^ (n + 1) - 1 := by
-- proof
  apply q_product_identity q n m hm

/--
[qBinomial_product_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma qBinomial_product_formula_eq
  [Field k]
  {q : k} :
-- imply
  ∀ (n m : ℕ), m ≤ n → qBinomial q n m * qFactorial q m = qFallingFact q n m := by
-- proof
  apply qBinomial_product_formula q

/--
[qFallingFact_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma qFallingFact_eq_zero_eq
  [Field k]
  {q : k}
  {n m : ℕ}
-- given
  (hqn : q ^ n = 1)
  (hm : 0 < m) :
-- imply
  qFallingFact q n m = 0 := by
-- proof
  apply qFallingFact_eq_zero q n m hqn hm

/--
[qFactorial_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma qFactorial_ne_zero_eq
  [Field k]
  {q : k}
  {n m : ℕ}
-- given
  (hq : IsPrimitiveRoot q n)
  (hm : m < n) :
-- imply
  qFactorial q m ≠ 0 := by
-- proof
  apply qFactorial_ne_zero q n m hq hm

/--
[qBinomial_vanish](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma qBinomial_vanish_eq
  [Field k]
  {q : k}
  {n : ℕ}
  {m : ℕ}
-- given
  (_hn : 1 < n)
  (hq : IsPrimitiveRoot q n)
  (hm1 : 0 < m)
  (hm2 : m < n) :
-- imply
  qBinomial q n m = 0 := by
-- proof
  apply qBinomial_vanish q n _hn hq m hm1 hm2

/--
[q_comm_pow_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma q_comm_pow_right_eq
  [Field k]
  [Ring A]
  [Algebra k A]
  {q : k}
  {a b : A}
-- given
  (hcomm : b * a = algebraMap k A q * (a * b)) :
-- imply
  ∀ m : ℕ, b ^ m * a = algebraMap k A (q ^ m) * (a * b ^ m) := by
-- proof
  apply q_comm_pow_right q a b hcomm

/--
[term_mul_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma term_mul_add_eq
  [Field k]
  [Ring A]
  [Algebra k A]
  {q : k}
  {a b : A}
  {c : k}
  {p m : ℕ}
-- given
  (hcomm : b * a = algebraMap k A q * (a * b)) :
-- imply
  algebraMap k A c * (a ^ p * b ^ m) * (a + b) = algebraMap k A (c * q ^ m) * (a ^ (p + 1) * b ^ m) + algebraMap k A c * (a ^ p * b ^ (m + 1)) := by
-- proof
  apply term_mul_add q a b hcomm c p m

/--
[q_binomial_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma q_binomial_expansion_eq
  [Field k]
  [Ring A]
  [Algebra k A]
  {q : k}
  {a b : A}
-- given
  (hcomm : b * a = algebraMap k A q * (a * b)) :
-- imply
  ∀ n : ℕ, (a + b) ^ n = ∑ m ∈ Finset.range (n + 1), algebraMap k A (qBinomial q n m) * (a ^ (n - m) * b ^ m) := by
-- proof
  apply q_binomial_expansion q a b hcomm

/--
[q_comm_power](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean)
-/
@[path]
private lemma q_comm_power_eq
  [Field k]
  [Ring A]
  [Algebra k A]
  {q : k}
  {n : ℕ}
  {a b : A}
-- given
  (hn : 1 < n)
  (hq : IsPrimitiveRoot q n)
  (hcomm : b * a = algebraMap k A q * (a * b)) :
-- imply
  (a + b) ^ n = a ^ n + b ^ n := by
-- proof
  apply q_comm_power q n hn hq a b hcomm


-- created on 2026-10-23
