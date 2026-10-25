/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Balanced.lean -/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Real.Basic
/-!
# Balanced graphs

A shared predicate for `D`-balanced (`D`-almost-regular) graphs.
-/


namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- A graph is `D`-balanced if its maximum degree is at most `D` times its
minimum degree. -/
def IsBalanced (G : SimpleGraph V) (D : ℝ) [DecidableRel G.Adj] : Prop :=
  G.maxDegree ≤ D * G.minDegree

end SimpleGraph
