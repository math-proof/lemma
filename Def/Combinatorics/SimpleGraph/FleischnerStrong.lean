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

/-- The edge positions of a cycle are in bijection with its support vertices. -/
noncomputable def IsCycle.finLengthEquivSupport {c : G.Walk x x}
    (hc : c.IsCycle) : Fin c.length ≃ {v // v ∈ c.support} := by
  classical
  have hlength : c.support.dropLast.length = c.length := by
    rw [List.length_dropLast, c.length_support]
    omega
  let eSupport : {v // v ∈ c.support.dropLast} ≃ {v // v ∈ c.support} := {
    toFun := fun v ↦ ⟨v, (hc.mem_dropLast_support_iff v).mp v.property⟩
    invFun := fun v ↦ ⟨v, (hc.mem_dropLast_support_iff v).mpr v.property⟩
    left_inv := fun _ ↦ Subtype.ext rfl
    right_inv := fun _ ↦ Subtype.ext rfl }
  exact (finCongr hlength.symm).trans
    ((hc.nodup_dropLast_support.getEquiv).trans eSupport)

/-- The graph induced by the vertices outside a closed walk. -/
def outsideGraph (c : G.Walk x x) : SimpleGraph {v // v ∉ c.support} :=
  G.induce {v | v ∉ c.support}

/-- The original vertices belonging to one connected component outside a closed walk. -/
def componentVertices (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) : Set V :=
  Subtype.val '' D.supp

def componentGraphHom (c : G.Walk x x)
    (D : c.outsideGraph.ConnectedComponent) :
    D.toSimpleGraph →g G.induce (c.componentVertices D) where
  toFun w := ⟨w.1.1, w.1, w.2, rfl⟩
  map_rel' := by
    intro u v huv
    exact huv

end Walk
end SimpleGraph
