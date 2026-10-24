/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/HypercubeExtremal.lean -/

import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card

/-!
# Hypercube Turán extremal number for `Q_n`

Primary source: Marko Pejić, *On the Turán Density of C10 in the Hypercube*,
arXiv:2608.12237v2 (defining text, lines 122-123, with subgraph and `H`-free
conventions at lines 136-140).

Scope: this file defines the `n`-dimensional hypercube `Q_n` as a Mathlib
`SimpleGraph` on `Fin n → Bool` and defines `ex(Q_n, H)` as the maximum edge
count over `H`-free `SimpleGraph.Subgraph`s, including non-spanning ones.
It proves the adjacency characterization, the lower bound into the maximum,
the upper bound by the edges of `Q_n`, attainment under nonemptiness, and the
`Q_0` boundary value. It does not formalize the asymptotic density, existence
of its limit, or the paper's `C_6`/`C_10` bounds.
-/

namespace SimpleGraph

/-- The `n`-dimensional hypercube `Q_n`: vertices are `Fin n → Bool`, with an edge
between two vertices exactly when they differ in exactly one coordinate. -/
def hypercubeGraph (n : ℕ) : SimpleGraph (Fin n → Bool) :=
  SimpleGraph.fromRel (fun x y => ∃! i, x i ≠ y i)

/-- The hypercube Turán number `ex(Q_n, H)`: the maximum edge count over all
`H`-free subgraphs of `Q_n`, as a total `Finset.sup` (zero when no witness exists). -/
noncomputable def hypercubeTuranNumber (n : ℕ) {W : Type*} (H : SimpleGraph W) : ℕ := by
  classical
  exact Finset.sup
    ((Finset.range ((hypercubeGraph n).edgeSet.ncard + 1)).filter
      (fun m => ∃ S : Subgraph (hypercubeGraph n), H.Free S.coe ∧ S.edgeSet.ncard = m))
    id
end SimpleGraph
