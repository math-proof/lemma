/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/CatalanHarmonicGeneratingFunction.lean -/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

section

open scoped BigOperators

namespace MetaMathlibExt

/-! # Generating function of Catalan numbers times harmonic numbers
-/

noncomputable def harm (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, (((k + 1 : ℕ) : ℝ)⁻¹)

noncomputable def cbR (n : ℕ) : ℝ := (Nat.centralBinom n : ℝ)

noncomputable def catR (n : ℕ) : ℝ := (catalan n : ℝ)

-- Series values
noncomputable def Aval (y : ℝ) : ℝ := ∑' n : ℕ, cbR n * y ^ n

noncomputable def Cval (y : ℝ) : ℝ := ∑' n : ℕ, catR n * y ^ n

noncomputable def Bval (y : ℝ) : ℝ := ∑' n : ℕ, cbR n * harm n * y ^ n

noncomputable def Fval (y : ℝ) : ℝ := ∑' n : ℕ, catR n * harm n * y ^ (n + 1)

-- Derivative term functions
noncomputable def dA (n : ℕ) (z : ℝ) : ℝ := cbR n * ((n : ℝ) * z ^ (n - 1))

noncomputable def dC (n : ℕ) (z : ℝ) : ℝ := catR n * ((n : ℝ) * z ^ (n - 1))

noncomputable def dB (n : ℕ) (z : ℝ) : ℝ := cbR n * harm n * ((n : ℝ) * z ^ (n - 1))

noncomputable def dF (n : ℕ) (z : ℝ) : ℝ := catR n * harm n * (((n : ℝ) + 1) * z ^ n)

noncomputable def S (y : ℝ) : ℝ := Real.sqrt (1 - 4*y)

end MetaMathlibExt
end
