/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ZeroDivisorGraph.lean -/

-- MathlibExt/RingTheory/ZeroDivisorGraph.lean
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Combinatorics.SimpleGraph.Basic
/-!
# Zero-divisor graph of a commutative ring

Formalizes the zero-divisor graph from Marco Caoduro and Meike Neuwohner,
[Boxicity and Threshold Dimension of Zero Divisor Graphs](https://arxiv.org/abs/2608.27381v1)
(formalized definition in `boxicity_arxiv.tex` lines 383–390):
vertices are the nonzero zero divisors and two vertices are
adjacent exactly when their product is zero.

The cited paper studies finite nonzero (commutative unital) rings,
while the reusable definition here works generally for any
commutative ring: the construction and proofs below require only
`CommRing R`, with no `Nontrivial R` or `Fintype R` hypotheses.
-/
universe u

namespace ZeroDivisorGraph

/-- Vertices are nonzero zero divisors, as a subtype of the ring. -/
abbrev Vertex (R : Type u) [CommRing R] :
    Type u := { r : R // r ≠ 0 ∧ r ∉ nonZeroDivisors R }

/-- Zero-divisor graph via the zero-product relation. -/
def zeroDivisorGraph (R : Type u) [CommRing R] :
    SimpleGraph (Vertex R) :=
  SimpleGraph.fromRel fun v w : Vertex R => (v : R) * (w : R) = 0
end ZeroDivisorGraph
