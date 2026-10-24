/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/InducedForestNumber.lean -/

import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Induced forest number

For a finite simple graph `G`, the induced forest number `a(G)` is the maximum
number of vertices in an induced forest, that is, the maximum cardinality of a
vertex set whose induced subgraph is acyclic.

Provenance: Heejae Jung, *A 15/31 Counterexample Family to the
Albertson--Berman Conjecture*, <https://arxiv.org/abs/2608.17350v1>.
Definition `a(G)` is in `disproving_albertson_berman_15_31.tex`, line 52.

Verified hashes (SHA-256):
* source bundle: `77e3f71bc75cef0408d82873e1625a059a0721bf24efa1c26d0f5daa034f77be`
* PDF: `af3e123b6a24073934ec014b51ddfcda779898b39169c104f075a299a937a1f8`
* source file `disproving_albertson_berman_15_31.tex`:
  `c1304969249c15dbe92171d3d26b7025a697bbba3a00bddae9428cf8d84c1145`
* line-52 span: `8af6e1d9bd63f3605f2bf89de6ede13e3af6933d9ce904ac181781e73b732d95`
-/

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- For a finite simple graph `G`, `inducedForestNumber G` is the maximum number
    of vertices in an induced forest, that is the maximum cardinality of a vertex
    set whose induced subgraph is acyclic. This is `a(G)` from the source. -/
noncomputable def inducedForestNumber (G : SimpleGraph V) : Nat := by
  classical
  exact Finset.sup (Finset.univ.powerset (α := V))
    (fun (s : Finset V) => if (G.induce (↑s : Set V)).IsAcyclic then s.card else 0)
end SimpleGraph
