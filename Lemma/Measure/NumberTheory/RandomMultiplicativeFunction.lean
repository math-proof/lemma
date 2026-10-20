import Mathlib
import sympy.Basic
import sympy.atlas.Probability.NumberTheory.RandomMultiplicativeFunction
open MeasureTheory ProbabilityTheory ArithmeticFunction
open scoped ENNReal
open MetaMathlibExt.RandomMultiplicativeFunction


/--
[rademacherMeasure_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma rademacherMeasure_singleton_eq
  {x : ℤˣ} :
-- imply
  rademacherMeasure {x} = (2 : ENNReal)⁻¹ := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.rademacherMeasure_singleton x

/--
[exists_rademacherFamily](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma exists_rademacherFamily_eq
  :
-- imply
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (X : Nat.Primes → Ω → ℤˣ),
    IsRademacherFamily μ X ∧ IsProbabilityMeasure μ := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.exists_rademacherFamily

/--
[primeSignNat_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma primeSignNat_prime_eq
  {X : Nat.Primes → Ω → ℤˣ}
  {p : ℕ}
  {ω : Ω}
-- given
  (hp : Nat.Prime p) :
-- imply
  primeSignNat X p ω = (X ⟨p, hp⟩ ω : ℤ) := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.primeSignNat_prime hp

/--
[primeSignNat_not_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma primeSignNat_not_prime_eq
  {X : Nat.Primes → Ω → ℤˣ}
  {n : ℕ}
  {ω : Ω}
-- given
  (hn : ¬Nat.Prime n) :
-- imply
  primeSignNat X n ω = 1 := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.primeSignNat_not_prime hn

/--
[IsRademacherFamily.measurable_primeSignNat](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma IsRademacherFamily_measurable_primeSignNat_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {X : Nat.Primes → Ω → ℤˣ}
  {n : ℕ}
-- given
  (hX : IsRademacherFamily μ X) :
-- imply
  Measurable (primeSignNat X n) := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.IsRademacherFamily.measurable_primeSignNat hX n

/--
[rademacherFunction_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma rademacherFunction_apply_eq
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω}
  {n : ℕ}
-- given
  (hn : n ≠ 0) :
-- imply
  rademacherFunction X ω n =
    ((moebius n : ℤ) ^ 2) * ∏ p ∈ n.primeFactors, primeSignNat X p ω := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.rademacherFunction_apply hn

/--
[rademacherFunction_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma rademacherFunction_one_eq
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω} :
-- imply
  rademacherFunction X ω 1 = 1 := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.rademacherFunction_one

/--
[rademacherFunction_eq_prod_of_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma rademacherFunction_eq_prod_of_squarefree_eq
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω}
  {n : ℕ}
-- given
  (hn : Squarefree n) :
-- imply
  rademacherFunction X ω n = ∏ p ∈ n.primeFactors, primeSignNat X p ω := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.rademacherFunction_eq_prod_of_squarefree hn

/--
[rademacherFunction_eq_zero_of_not_squarefree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma rademacherFunction_eq_zero_of_not_squarefree_eq
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω}
  {n : ℕ}
-- given
  (hn : ¬Squarefree n) :
-- imply
  rademacherFunction X ω n = 0 := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.rademacherFunction_eq_zero_of_not_squarefree hn

/--
[isMultiplicative_rademacherFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma isMultiplicative_rademacherFunction_eq
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω} :
-- imply
  IsMultiplicative (rademacherFunction X ω) := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.isMultiplicative_rademacherFunction

/--
[rademacherFunction_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma rademacherFunction_prime_eq
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω}
  {p : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  rademacherFunction X ω p = primeSignNat X p ω := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.rademacherFunction_prime hp

/--
[rademacherFunction_prime_sq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma rademacherFunction_prime_sq_eq
  {X : Nat.Primes → Ω → ℤˣ}
  {ω : Ω}
  {p : ℕ}
-- given
  (hp : Nat.Prime p) :
-- imply
  rademacherFunction X ω (p ^ 2) = 0 := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.rademacherFunction_prime_sq hp

/--
[IsRademacherFamily.measurable_rademacherFunction](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Probability/NumberTheory/RandomMultiplicativeFunction.lean)
-/
@[path]
private lemma IsRademacherFamily_measurable_rademacherFunction_eq
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  {X : Nat.Primes → Ω → ℤˣ}
  {n : ℕ}
-- given
  (hX : IsRademacherFamily μ X) :
-- imply
  Measurable (fun ω => rademacherFunction X ω n) := by
-- proof
  apply MetaMathlibExt.RandomMultiplicativeFunction.IsRademacherFamily.measurable_rademacherFunction hX n


-- created on 2026-10-20
