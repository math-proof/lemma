/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Sequences
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Completion
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.Data.Finsupp.Basic
public import Mathlib.Analysis.Normed.Module.Completion
public import Mathlib.Analysis.InnerProductSpace.MeanErgodic
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Dynamics.BirkhoffSum.Basic
public import Mathlib.Dynamics.BirkhoffSum.Average
public import Mathlib.Topology.Algebra.LinearMapCompletion
public import Mathlib.Topology.Algebra.Module.Basic
public import Theorem.Combinatorics.Additive.Sarkozy

@[expose] public section

namespace MathlibExt.Combinatorics.Additive.SarkozyWanted

open scoped InnerProductSpace

/-- Correlation count: pairs in `A_N × A_N` with difference `d`. -/
noncomputable def sarkozyCorr (A : Set ℕ) (N : ℕ) (d : ℤ) : ℕ :=
  (((sarkozyFin A N) ×ˢ (sarkozyFin A N)).filter
    (fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ) = d)).card

/-- Image of `A_N × s` under `(a, i) ↦ a - e i`. -/
noncomputable def sarkozyIm {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) : Finset ℤ :=
  ((sarkozyFin A N) ×ˢ s).image (fun p : ℕ × ι => (p.1 : ℤ) - e p.2)

/-- Fiber weight for the sum-of-squares identity. -/
noncomputable def sarkozyW {ι : Type*} (A : Set ℕ) (N : ℕ) (s : Finset ι)
    (e : ι → ℤ) (c : ι → ℝ) (t : ℤ) : ℝ :=
  ∑ a ∈ sarkozyFin A N, ∑ i ∈ s, (if (a : ℤ) - e i = t then c i else 0)

end MathlibExt.Combinatorics.Additive.SarkozyWanted
