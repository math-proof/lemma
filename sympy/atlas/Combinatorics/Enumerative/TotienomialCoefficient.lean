/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/TotienomialCoefficient.lean -/

import Mathlib.Data.Nat.Totient

/-!
Verified Edgar-Spivey JIS source:
https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex

Generalized f-factorial and f-binomial coefficient, plus the
totienomial specialization to Euler's phi function.
-/

namespace MetaMathlibExt

/-- Generalized factorial: product of `f i` for `i = 1, .., n`, empty product `= 1`.
Source: https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex -/
def generalizedFactorial (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  Finset.prod (Finset.Icc 1 n) f

/-- The source-domain condition on `f`: positive indices have positive values. -/
def IsPositiveSequence (f : ℕ → ℕ) : Prop :=
  ∀ i, 0 < i → 0 < f i

/-- A generalized factorial is positive when `f` has the source's positive range. -/
theorem generalizedFactorial_pos {f : ℕ → ℕ} (hf : IsPositiveSequence f) (n : ℕ) :
    0 < generalizedFactorial f n := by
  apply Finset.prod_pos
  intro i hi
  exact hf i (Finset.mem_Icc.mp hi).1

/-- Totalized generalized binomial coefficient.  On the source domain, where `f i > 0`
for every positive `i`, this is the source's exact quotient.  For arbitrary Nat-valued `f`,
Lean's rational division convention extends the definition by returning zero when the
denominator is zero.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex -/
def generalizedBinomialCoefficient (f : ℕ → ℕ) (n m : ℕ) : ℚ :=
  (generalizedFactorial f (n + m) : ℚ) /
    ((generalizedFactorial f n : ℚ) * (generalizedFactorial f m : ℚ))

/-- On positive-valued sequences, the totalized definition satisfies the source's defining
quotient equation with a nonzero denominator. -/
theorem generalizedBinomialCoefficient_mul_denominator {f : ℕ → ℕ}
    (hf : IsPositiveSequence f) (n m : ℕ) :
    generalizedBinomialCoefficient f n m *
        ((generalizedFactorial f n : ℚ) * (generalizedFactorial f m : ℚ)) =
      generalizedFactorial f (n + m) := by
  apply div_mul_cancel₀
  exact mul_ne_zero
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (generalizedFactorial_pos hf n)))
    (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (generalizedFactorial_pos hf m)))

/-- Totienomial coefficient: the generalized binomial coefficient at Euler's `phi`.
The values `Nat.totient i` are positive for positive `i`, so this specialization lies in the
source domain rather than the totalized zero-denominator extension.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL19/Edgar/edgar3.tex -/
def totienomialCoefficient (n m : ℕ) : ℚ :=
  generalizedBinomialCoefficient Nat.totient n m

end MetaMathlibExt
