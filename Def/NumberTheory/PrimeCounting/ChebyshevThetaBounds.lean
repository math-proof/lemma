/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ChebyshevThetaBounds.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.MeanInequalities
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Misc
open Nat hiding log
open Finset Real
open ArithmeticFunction hiding log id


/-- Chebyshev's 30-weight constant. -/
noncomputable def ctbA0 : ℝ :=
  (1 / 2) * Real.log 2 + (1 / 3) * Real.log 3 + (1 / 5) * Real.log 5 -
    (1 / 30) * Real.log 30

/-- Chebyshev's combination weight `m - m/2 - m/3 - m/5 + m/30` (ℕ-division). -/
def ctbW (m : ℕ) : ℤ :=
  (m : ℤ) - ((m / 2 : ℕ) : ℤ) - ((m / 3 : ℕ) : ℤ) - ((m / 5 : ℕ) : ℤ) +
    ((m / 30 : ℕ) : ℤ)

/-- Chebyshev's combination `U(N)` of log-factorials. -/
noncomputable def ctbU (N : ℕ) : ℝ :=
  Real.log (N ! : ℝ) - Real.log ((N / 2)! : ℝ) - Real.log ((N / 3)! : ℝ) -
    Real.log ((N / 5)! : ℝ) + Real.log ((N / 30)! : ℝ)

