/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanHarmonicGeneratingFunction.lean -/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.ModuleTopology

section
open scoped BigOperators

namespace MetaMathlibExt

/-! # Generating function of Catalan numbers times harmonic numbers
-/

private noncomputable def harm (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ)⁻¹)
private noncomputable def cbR (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ)
private noncomputable def catR (n : ℕ) : ℝ := (catalan n : ℝ)

-- Series values
private noncomputable def Aval (y : ℝ) : ℝ := ∑' n : ℕ, cbR n * y ^ n
private noncomputable def Cval (y : ℝ) : ℝ := ∑' n : ℕ, catR n * y ^ n
private noncomputable def Bval (y : ℝ) : ℝ := ∑' n : ℕ, cbR n * harm n * y ^ n
private noncomputable def Fval (y : ℝ) : ℝ := ∑' n : ℕ, catR n * harm n * y ^ (n + 1)

-- Derivative term functions
private noncomputable def dA (n : ℕ) (z : ℝ) : ℝ := cbR n * ((n : ℝ) * z ^ (n - 1))
private noncomputable def dC (n : ℕ) (z : ℝ) : ℝ := catR n * ((n : ℝ) * z ^ (n - 1))
private noncomputable def dB (n : ℕ) (z : ℝ) : ℝ := cbR n * harm n * ((n : ℝ) * z ^ (n - 1))
private noncomputable def dF (n : ℕ) (z : ℝ) : ℝ := catR n * harm n * (((n : ℝ) + 1) * z ^ n)

private noncomputable def S (y : ℝ) : ℝ := Real.sqrt (1 - 4*y)
end MetaMathlibExt
end
