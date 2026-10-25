/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/ConvexDistance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.Convex.Topology
set_option maxHeartbeats 800000

open scoped BigOperators
open Finset


namespace ConvexDistance

variable {n : ℕ}

/-- The $n$-dimensional unit cube $[0,1]^n$ as a subset of $\mathbb{R}^n$. -/
def unitCube (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i : Fin n, 0 ≤ x i ∧ x i ≤ 1}

/-- Weighted Hamming distance from $x$ to $y$ with weight vector $\alpha$:
$\sum_{i : x_i \neq y_i} |\alpha_i|$. -/
noncomputable def weightedHammingDist (α x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, if x i ≠ y i then |α i| else 0

/-- Weighted Hamming distance from $x$ to a set $A$: the infimum of `weightedHammingDist α x y`
as $y$ ranges over $A$. -/
noncomputable def weightedHammingDistSet (α x : EuclideanSpace ℝ (Fin n))
    (A : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sInf ((weightedHammingDist α x) '' A)

/-- Talagrand's convex distance from $x$ to a set $A$: the supremum over unit vectors
$\alpha$ of the $\alpha$-weighted Hamming distance from $x$ to $A$. -/
noncomputable def talagrandDist (x : EuclideanSpace ℝ (Fin n))
    (A : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  sSup ((fun α => weightedHammingDistSet α x A) '' {α | ‖α‖ = 1})

end ConvexDistance
