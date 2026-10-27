import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.NumberTheory.NicolNumber
open MetaMathlibExt
open scoped BigOperators


/--
[test_not_nicol_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NicolNumber.lean)
-/
@[path]
private lemma test_not_nicol_zero : ¬ IsNicolNumber 0 := by
  simp [IsNicolNumber]

/--
[test_nicol_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NicolNumber.lean)
-/
@[path]
private lemma test_nicol_one : IsNicolNumber 1 :=
⟨by norm_num, one_dvd _⟩

/--
[test_t_nicol_two_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NicolNumber.lean)
-/
@[path]
private lemma test_t_nicol_two_one : IsTNicolNumber 2 1 := by
  refine ⟨by norm_num, ?_⟩
  norm_num [Nat.totient_one, Nat.divisors_one, Finset.sum_singleton]

/--
[test_unfold_nicol](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NicolNumber.lean)
-/
@[path]
private lemma test_unfold_nicol (n : ℕ) :
  IsNicolNumber n ↔ 0 < n ∧ n ∣ Nat.totient n + ∑ d ∈ n.divisors, d :=
  Iff.rfl

/--
[test_unfold_t_nicol](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NicolNumber.lean)
-/
@[path]
private lemma test_unfold_t_nicol (t n : ℕ) :
  IsTNicolNumber t n ↔
    0 < n ∧ Nat.totient n + ∑ d ∈ n.divisors, d = t * n :=
  Iff.rfl


-- created on 2026-10-23
