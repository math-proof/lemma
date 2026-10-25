/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Data.Finset.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Tactic
import Mathlib.Topology.Constructions
import Mathlib.Topology.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.Finsupp.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.Supported
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Algebra.Module.Basic
import Theorem.Combinatorics.Additive.Sarkozy


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
