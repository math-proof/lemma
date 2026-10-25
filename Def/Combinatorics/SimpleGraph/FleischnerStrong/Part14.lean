/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Def.Combinatorics.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.StrongSquareCycle
import Lemma.SimpleGraph.VertexConnectivity
import Lemma.SimpleGraph.Contraction
import Lemma.SimpleGraph.EdgeIndexedMultigraph
import Lemma.SimpleGraph.Riha
import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
import Def.Combinatorics.SimpleGraph.Riha
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Sum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.ZMod.Basic
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part8
/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/

/-! ## CycleComplement -/


namespace SimpleGraph

namespace Walk

variable {V : Type*} {G : SimpleGraph V} {x : V}

noncomputable def cycleCopyIncidenceEquiv {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) :
    {e : c.CycleCopyEdge q // (c.cycleCopyMultigraph q).Inc (c.getVert i) e} ≃
      Fin (q.copies (i - 1)) ⊕ Fin (q.copies i) where
  toFun := cycleCopyIncidenceTo hc q i
  invFun := cycleCopyIncidenceFrom hc q i
  left_inv := cycleCopyIncidence_leftInverse hc q i
  right_inv := cycleCopyIncidence_rightInverse hc q i

end Walk

end SimpleGraph

namespace SimpleGraph

namespace Walk

/-- The canonical copy choices that correct the trail-system degrees on a cycle. -/
noncomputable def cycleEulerizationCompletion [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle) [NeZero c.length]
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :
    CyclicParityCompletion
      (fun i : Fin c.length ↦ (c.trailSystemMultigraph cover).degree (c.getVert i)) :=
  cyclicParityCompletion _ (c.trailSystemMultigraph_cycle_degree_sum_even hc cover)

/-- The Step A trail system together with its parity-correcting cycle-edge copies. -/
noncomputable def cycleEulerizationMultigraph [Finite V]
    (c : G.Walk x x) (hc : c.IsCycle) [NeZero c.length]
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D) :=
  (c.trailSystemMultigraph cover).disjointSum
    (c.cycleCopyMultigraph (c.cycleEulerizationCompletion hc cover))

end Walk
end SimpleGraph
