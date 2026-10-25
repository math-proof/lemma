import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Convex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructions
import Theorem.Analysis.Convex.FenchelMoreau
/-!
# Fenchel conjugates and epigraph API

Foundation for the Fenchel–Moreau theorem: a proper lsc convex
`f : E → EReal` on a Hausdorff locally convex real tvs equals its
biconjugate. This module provides the conjugate/biconjugate definitions in
the exact shape of `banach_limit`-style wanted statements and the
closed-epigraph API (convexity is definitional from the hypothesis;
closedness is the continuous preimage of the `EReal` epigraph).

References: Werner Fenchel, *Convex Cones, Sets, and Functions: From Notes
by D. W. Blackett of Lectures at Princeton University, 1951*, Princeton
University Department of Mathematics, 1953, Open Library OL1430688W; and
Jean-Jacques Moreau, "Fonctions convexes duales et points proximaux,"
C. R. Acad. Sci. Paris 255 (1962), 2897–2899, zbMATH 0118.10502.
-/


namespace Convex.FenchelMoreau

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [T2Space E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E]

/-- Effective domain: points where `f` is not `⊤`. -/
def dom (f : E → EReal) : Set E := {y | f y ≠ ⊤}

end Convex.FenchelMoreau
