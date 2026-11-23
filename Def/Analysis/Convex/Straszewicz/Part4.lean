-- Author: @toskua, Avocado
-- Provenance: Adam Kiezun authored the original formalization
-- (commit 8a13ba393c1d23f85b900081c600941a4bdd56dc); @toskua, Avocado
-- authored only the Convexity.StdSimplex representation migration.

module

public import Mathlib.Analysis.Convex.Caratheodory
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Convex.Slope
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Baire.Lemmas
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Tactic.Module
public import Mathlib.Topology.Bases
public import Theorem.Analysis.Convex.Straszewicz.Part3

@[expose] public section

/-!
# Straszewicz's theorem on exposed points

Every extreme point of a compact convex set in a finite-dimensional real
normed space lies in the closure of its exposed points.

Primary source: S. Straszewicz, "Über exponierte Punkte abgeschlossener
Punktmengen", Fundamenta Mathematicae 24 (1935), 139–143,
DOI 10.4064/FM-24-1-139-143.
-/


namespace Convex.Straszewicz

open Set Metric Filter TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E}

section Support

variable {K : Set E}

/-- Gateaux points: both opposite directional derivatives sum nonpositively. -/
def GateauxPt (h : StrongDual ℝ E → ℝ) (x : StrongDual ℝ E) : Prop :=
  ∀ v, dirDeriv h x v + dirDeriv h x (-v) ≤ 0

end Support
end Convex.Straszewicz
