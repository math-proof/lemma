/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeInterval/Breusch/Lower.lean -/

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Data.Nat.Cast.Field
import Def.NumberTheory.PrimeInterval.Breusch.Grid
import Lemma.Nat.PrimeInterval.Breusch.Grid
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-!
# Breusch weighted-product lower bound

Stirling bounds for factorials and the Möbius-weighted binomial-product lower
bound `logF9`, following the `k = 9`, `Q = 210` case of Breusch's argument.
-/


namespace MathlibExt.NumberTheory.BreuschWanted.Internal

/-- Scaled factorial argument `10 * n * (Q9 / m)`. -/
def N10m (m n : ℕ) : ℕ := 10 * n * (Q9 / m)

/-- Scaled factorial argument `9 * n * (Q9 / m)`. -/
def N9m (m n : ℕ) : ℕ := 9 * n * (Q9 / m)

/-- Scaled factorial argument `n * (Q9 / m)`. -/
def N1m (m n : ℕ) : ℕ := n * (Q9 / m)

/-- Binomial factor `(N10m)! / ((N9m)! * (N1m)!)`. -/
def ratio9 (m n : ℕ) : ℕ := (N10m m n)! / ((N9m m n)! * (N1m m n)!)

/-- Logarithm of the Möbius-weighted product `F_9(n)`. -/
noncomputable def logF9 (n : ℕ) : ℝ :=
  w9.toFinset.sum (fun q : ℕ × ℤ => (q.2 : ℝ) * Real.log ((ratio9 q.1 n : ℕ) : ℝ))

/-- Main Stirling term `x * log x - x`. -/
noncomputable def fmain (x : ℝ) : ℝ := x * Real.log x - x

/-- Constant error term from `log q.1` in the `Z9` computation. -/
noncomputable def K9 : ℝ :=
  w9.toFinset.sum (fun q : ℕ × ℤ => (q.2 : ℝ) * Real.log (q.1 : ℝ) / (q.1 : ℝ))

end MathlibExt.NumberTheory.BreuschWanted.Internal
