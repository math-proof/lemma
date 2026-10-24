/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/EulerProductMeanValue.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Interval.Finset.Basic
import Lemma.Nat.ArithmeticFunction.WintnerMeanValue
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace MetaMathlibExt

/-- Coordinate restriction of `f` to the `i`-th coordinate, as an arithmetic
function: `emvF f i m = f (Function.update 1 i m)` for `m ≠ 0`. -/
private noncomputable def emvF {k : ℕ} (f : (Fin k → ℕ) → ℂ) (i : Fin k) :
    ArithmeticFunction ℂ :=
  ⟨fun m => if m = 0 then 0 else f (Function.update 1 i m), rfl⟩

/-- Moebius convolution factor `μ * emvF f i`, with the same coercion as in
`wintner_mean_value`. -/
private noncomputable def emvG {k : ℕ} (f : (Fin k → ℕ) → ℂ) (i : Fin k) :
    ArithmeticFunction ℂ :=
  (↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * emvF f i
end MetaMathlibExt
