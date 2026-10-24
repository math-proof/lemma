/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/TotienomialCoefficient.lean -/

import sympy.atlas.Combinatorics.Enumerative.TotienomialCoefficient
import Lemma.Finset.Enumerative.TotienomialCoefficient
import Mathlib.Tactic.NormNum

-- Empty products.
example : MetaMathlibExt.generalizedFactorial (fun i => i) 0 = 1 := by decide
example : MetaMathlibExt.generalizedFactorial Nat.totient 0 = 1 := by decide
example : MetaMathlibExt.generalizedBinomialCoefficient (fun i => i) 0 3 = 1 := by
  have h0 : MetaMathlibExt.generalizedFactorial (fun i => i) 0 = 1 := by decide
  have h03 : MetaMathlibExt.generalizedFactorial (fun i => i) (0 + 3) = 6 := by decide
  simp only [MetaMathlibExt.generalizedBinomialCoefficient, h03, h0]
  norm_num
example : MetaMathlibExt.totienomialCoefficient 0 0 = 1 := by
  have h00 : MetaMathlibExt.generalizedFactorial Nat.totient (0 + 0) = 1 := by decide
  simp only [MetaMathlibExt.totienomialCoefficient,
    MetaMathlibExt.generalizedBinomialCoefficient, h00, Nat.cast_one,
    mul_one, div_one]

-- Identity-function specialization is the ordinary factorial / binomial.
example : MetaMathlibExt.generalizedFactorial (fun i => i) 4 = 24 := by decide
example : MetaMathlibExt.generalizedBinomialCoefficient (fun i => i) 2 2 = 6 := by
  have h2 : MetaMathlibExt.generalizedFactorial (fun i => i) 2 = 2 := by decide
  have h22 : MetaMathlibExt.generalizedFactorial (fun i => i) (2 + 2) = 24 := by decide
  simp only [MetaMathlibExt.generalizedBinomialCoefficient, h22, h2]
  norm_num

-- The source-domain invariant makes the denominator nonzero and recovers the exact quotient.
example : MetaMathlibExt.IsPositiveSequence (fun i => i) := by
  intro i hi
  exact hi

example : MetaMathlibExt.generalizedBinomialCoefficient (fun i => i) 2 2 *
      ((MetaMathlibExt.generalizedFactorial (fun i => i) 2 : ℚ) *
        MetaMathlibExt.generalizedFactorial (fun i => i) 2) =
    MetaMathlibExt.generalizedFactorial (fun i => i) (2 + 2) :=
  MetaMathlibExt.generalizedBinomialCoefficient_mul_denominator (by
    intro i hi
    exact hi) 2 2

-- The deliberately totalized extension returns zero when a positive-index value is zero.
example : MetaMathlibExt.generalizedBinomialCoefficient (fun _ => 0) 1 1 = 0 := by
  simp [MetaMathlibExt.generalizedBinomialCoefficient,
    MetaMathlibExt.generalizedFactorial]

-- Representative totienomial values: phi on 1..5 = 1, 1, 2, 2, 4.
example : MetaMathlibExt.generalizedFactorial Nat.totient 4 = 4 := by decide
example : MetaMathlibExt.totienomialCoefficient 2 1 = 2 := by
  have h1 : MetaMathlibExt.generalizedFactorial Nat.totient 1 = 1 := by decide
  have h2 : MetaMathlibExt.generalizedFactorial Nat.totient 2 = 1 := by decide
  have h21 : MetaMathlibExt.generalizedFactorial Nat.totient (2 + 1) = 2 := by decide
  simp only [MetaMathlibExt.totienomialCoefficient,
    MetaMathlibExt.generalizedBinomialCoefficient, h21, h2, h1]
  norm_num
example : MetaMathlibExt.totienomialCoefficient 3 2 = 8 := by
  have h3 : MetaMathlibExt.generalizedFactorial Nat.totient 3 = 2 := by decide
  have h2 : MetaMathlibExt.generalizedFactorial Nat.totient 2 = 1 := by decide
  have h32 : MetaMathlibExt.generalizedFactorial Nat.totient (3 + 2) = 16 := by decide
  simp only [MetaMathlibExt.totienomialCoefficient,
    MetaMathlibExt.generalizedBinomialCoefficient, h32, h3, h2]
  norm_num

-- Nonintegral rational quotient: f(i) = i + 1 at n = m = 1 gives 6 / (2 * 2) = 3 / 2.
example : MetaMathlibExt.generalizedBinomialCoefficient (fun i => i + 1) 1 1 = 3 / 2 := by
  have h1 : MetaMathlibExt.generalizedFactorial (fun i => i + 1) 1 = 2 := by decide
  have h2 : MetaMathlibExt.generalizedFactorial (fun i => i + 1) (1 + 1) = 6 := by decide
  simp only [MetaMathlibExt.generalizedBinomialCoefficient, h1, h2]
  norm_num
