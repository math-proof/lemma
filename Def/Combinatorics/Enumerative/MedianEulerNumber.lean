/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianEulerNumber.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.ModEq
public import Def.Combinatorics.Enumerative.EulerSeidelMatrix
public import Theorem.Finset.Enumerative.EulerSeidelMatrix
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Median Euler numbers

Sources:
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen53.tex> and
<https://cs.uwaterloo.ca/journals/JIS/VOL6/Chen/chen50.tex>.
-/


namespace MetaMathlibExt

open scoped BigOperators

/-- Successive Euler coefficients used to define the median Euler numbers.

This is the memoized coefficient recurrence obtained from
`E * cosh = 1 + sinh`. Concept `jis_sem_0f85ae780217af7de3a4a1b6`; statements
`jis_bdf7050da9616e789767cc45` and `jis_acae886a10f953dc872dd3f5`. -/
def medianEulerCoefficients : ℕ → List ℤ
  | 0 => [1]
  | n + 1 =>
      let previous := medianEulerCoefficients n
      let N := n + 1
      let sum : ℤ :=
        ∑ j ∈ Finset.filter (fun j => 2 ≤ j ∧ j % 2 = 0) (Finset.range (N + 1)),
          (N.choose j : ℤ) * previous.getD (N - j) 0
      previous ++ [(if N % 2 = 1 then 1 else 0) - sum]

/-- Euler coefficient `E_n` in `sech x + tanh x = ∑ n, E_n x^n / n!`. -/
def medianEulerCoeff (n : ℕ) : ℤ :=
  (medianEulerCoefficients n).getD n 0

/-- Initial row for the Euler-Seidel matrix defining the median Euler numbers. -/
def medianEulerInitialRow : ℕ → ℤ
  | 0 => 0
  | m + 1 => medianEulerCoeff (m + 1)

/-- Median Euler number `R_n`, the absolute value of the indicated Euler-Seidel entry. -/
def medianEulerNumber (n : ℕ) : ℕ :=
  (eulerSeidelMatrix medianEulerInitialRow (n + 1) n).natAbs

-- Abbreviations for the EGFs of `E` and `a`.
def meE : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((medianEulerCoeff n : ℤ) : ℚ) / (n.factorial : ℚ)

def meA : PowerSeries ℚ :=
  PowerSeries.mk fun n => ((medianEulerInitialRow n : ℤ) : ℚ) / (n.factorial : ℚ)

end MetaMathlibExt
