/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/OppermannCyclicNumbers.lean -/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Order.Interval.Finset.Nat
/-!
# Cyclic numbers and Oppermann interval counts

These definitions support Joel E. Cohen, *Conjectures about Primes and
Cyclic Numbers*, Journal of Integer Sequences 28 (2025), Article 25.4.1.
-/


namespace MetaMathlibExt

/-- A positive integer `n` is cyclic when `gcd(n, φ(n)) = 1`. -/
def IsCyclicNumber (n : ℕ) : Prop :=
  0 < n ∧ n.Coprime n.totient

/-- The number of cyclic integers in the closed interval `[n²-n, n²]`. -/
def oppermannCyclicCountLeft (n : ℕ) : ℕ :=
  letI : DecidablePred IsCyclicNumber := fun k => by
    unfold IsCyclicNumber
    infer_instance
  ((Finset.Icc (n ^ 2 - n) (n ^ 2)).filter IsCyclicNumber).card

/-- The number of cyclic integers in the closed interval `[n², n²+n]`. -/
def oppermannCyclicCountRight (n : ℕ) : ℕ :=
  letI : DecidablePred IsCyclicNumber := fun k => by
    unfold IsCyclicNumber
    infer_instance
  ((Finset.Icc (n ^ 2) (n ^ 2 + n)).filter IsCyclicNumber).card

/-- The source's first left-hand asymptotic approximation. -/
noncomputable def oppermannCyclicLeftApproximation (x : ℝ) : ℝ :=
  x / (Real.exp Real.eulerMascheroniConstant *
    Real.log (Real.log (Real.log (x ^ 2)))) *
    (1 - Real.eulerMascheroniConstant /
      Real.log (Real.log (Real.log (x ^ 2))))

/-- The simplified asymptotic approximation shared by both intervals. -/
noncomputable def oppermannCyclicApproximation (x : ℝ) : ℝ :=
  x / (Real.exp Real.eulerMascheroniConstant *
    Real.log (Real.log (Real.log x))) *
    (1 - Real.eulerMascheroniConstant /
      Real.log (Real.log (Real.log x)))

/-- The source's first right-hand asymptotic approximation. -/
noncomputable def oppermannCyclicRightApproximation (x : ℝ) : ℝ :=
  x / (Real.exp Real.eulerMascheroniConstant *
    Real.log (Real.log (Real.log (x * (x + 1))))) *
    (1 - Real.eulerMascheroniConstant /
      Real.log (Real.log (Real.log (x * (x + 1)))))

end MetaMathlibExt
