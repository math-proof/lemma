module
public import Def.Combinatorics.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.StrongSquareCycle
public import Theorem.SimpleGraph.VertexConnectivity
public import Theorem.SimpleGraph.Contraction
public import Theorem.SimpleGraph.EdgeIndexedMultigraph
public import Theorem.SimpleGraph.Riha
public import Theorem.Combinatorics.SimpleGraph.VertexConnectivity
public import Theorem.Combinatorics.SimpleGraph.Contraction.Part3
public import Def.Combinatorics.SimpleGraph.EdgeIndexedMultigraph.Part4
public import Def.Combinatorics.SimpleGraph.Riha
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Group.Nat.Even
public import Mathlib.Basic.Finite.Sigma
public import Mathlib.Basic.Finite.Sum
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Data.List.ChainOfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.Data.ZMod.Basic
public import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part8


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/FleischnerStrong.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
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
