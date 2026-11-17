/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/EulerProductMeanValue.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.NumberTheory.EulerProduct.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecialFunctions.Exponential

@[expose] public section

namespace MetaMathlibExt

/-- Coordinate restriction of `f` to the `i`-th coordinate, as an arithmetic
function: `emvF f i m = f (Function.update 1 i m)` for `m ≠ 0`. -/
noncomputable def emvF {k : ℕ} (f : (Fin k → ℕ) → ℂ) (i : Fin k) :
    ArithmeticFunction ℂ :=
  ⟨fun m => if m = 0 then 0 else f (Function.update 1 i m), rfl⟩

/-- Moebius convolution factor `μ * emvF f i`, with the same coercion as in
`wintner_mean_value`. -/
noncomputable def emvG {k : ℕ} (f : (Fin k → ℕ) → ℂ) (i : Fin k) :
    ArithmeticFunction ℂ :=
  (↑ArithmeticFunction.moebius : ArithmeticFunction ℂ) * emvF f i

end MetaMathlibExt
