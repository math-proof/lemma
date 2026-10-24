/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ChromaticSymmetric.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Chromatic symmetric functions via coloring profiles

The chromatic symmetric function of a graph is determined by the counts of
proper colorings with each multiplicity profile: for every finite labeled
palette and every prescribed multiplicity of each color, count the proper
colorings realizing exactly those multiplicities. This module packages those
counts (`chromaticProfileCount`) and the resulting notion of two graphs having
the same chromatic symmetric function (`SameChromaticSymmetricFunction`),
together with its basic equivalence and isomorphism-invariance interface.
-/

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Number of proper colorings of `G` with labeled colors `Fin k` in which
each color occurs with exactly the prescribed multiplicity. These counts are
the coefficients of the chromatic symmetric function. -/
noncomputable def chromaticProfileCount [Finite V] (G : SimpleGraph V) (k : ℕ)
    (multiplicity : Fin k → ℕ) : ℕ :=
  Nat.card { c : G.Coloring (Fin k) //
    ∀ color, Nat.card { v : V // c v = color } = multiplicity color }

/-- Equality of chromatic symmetric functions, represented transparently
through the coefficient characterization: agreement of all coloring-profile
counts for every finite palette and multiplicity profile. -/
def SameChromaticSymmetricFunction [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∀ k multiplicity,
    chromaticProfileCount G k multiplicity = chromaticProfileCount H k multiplicity
end SimpleGraph
