/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/ZeroDivisorGraph.lean -/

-- MathlibExt/RingTheory/ZeroDivisorGraph.lean

module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Abbrev.RingTheory.ZeroDivisorGraph

@[expose] public section

universe u

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


namespace ZeroDivisorGraph

/-- Zero-divisor graph via the zero-product relation. -/
def zeroDivisorGraph (R : Type u) [CommRing R] :
    SimpleGraph (Vertex R) :=
  SimpleGraph.fromRel fun v w : Vertex R => (v : R) * (w : R) = 0

end ZeroDivisorGraph
