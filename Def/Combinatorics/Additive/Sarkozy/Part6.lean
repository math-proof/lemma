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
public import Theorem.Combinatorics.Additive.Sarkozy.Part4

@[expose] public section

namespace MathlibExt.Combinatorics.Additive.SarkozyWanted

open scoped InnerProductSpace

/-- Fixed-point submodule of a power of an isometry (N9–N12 setup). -/
def sarkozyFix {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (U : H →ₗᵢ[ℝ] H) (m : ℕ) : Submodule ℝ H :=
  LinearMap.eqLocus ((U ^ m).toLinearMap) LinearMap.id

/-- Closed span of all nontrivial fixed-point submodules (N9–N12 setup). -/
def sarkozyWclos {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (U : H →ₗᵢ[ℝ] H) : Submodule ℝ H :=
  (⨆ j : ℕ, sarkozyFix U (j + 1)).topologicalClosure

end MathlibExt.Combinatorics.Additive.SarkozyWanted
