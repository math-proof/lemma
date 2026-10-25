/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/Straszewicz.lean -/

-- Author: @toskua, Avocado
-- Provenance: Adam Kiezun authored the original formalization
-- (commit 8a13ba393c1d23f85b900081c600941a4bdd56dc); @toskua, Avocado
-- authored only the Convexity.StdSimplex representation migration.

import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic.Module
import Mathlib.Topology.Bases
/-!
# Straszewicz's theorem on exposed points

Every extreme point of a compact convex set in a finite-dimensional real
normed space lies in the closure of its exposed points.

Primary source: S. Straszewicz, "Über exponierte Punkte abgeschlossener
Punktmengen", Fundamenta Mathematicae 24 (1935), 139–143,
DOI 10.4064/FM-24-1-139-143.
-/


namespace MathlibExt.Analysis.Convex.Straszewicz

open Set Metric Filter TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Difference quotients whose infimum is the directional derivative. -/
noncomputable def dirQuot (h : StrongDual ℝ E → ℝ) (x v : StrongDual ℝ E) : Set ℝ :=
  (fun t : ℝ => (h (x + t • v) - h x) / t) '' Ioi 0

/-- Directional derivative of a convex function as an infimum of quotients. -/
noncomputable def dirDeriv (h : StrongDual ℝ E → ℝ) (x v : StrongDual ℝ E) : ℝ :=
  sInf (dirQuot h x v)

variable {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E}

section Support

/-- Support function of a compact set. -/
noncomputable def suppFunc (K : Set E) : StrongDual ℝ E → ℝ :=
  fun l => sSup ((fun x => l x) '' K)

/-- Gateaux points: both opposite directional derivatives sum nonpositively. -/
def GateauxPt (h : StrongDual ℝ E → ℝ) (x : StrongDual ℝ E) : Prop :=
  ∀ v, dirDeriv h x v + dirDeriv h x (-v) ≤ 0

end Support
end MathlibExt.Analysis.Convex.Straszewicz
