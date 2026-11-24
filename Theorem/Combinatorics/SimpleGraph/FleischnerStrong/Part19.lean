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
public import Structure.Combinatorics.SimpleGraph.FleischnerStrong.Part8


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

namespace EdgeIndexedMultigraph

namespace IndexedWalk

theorem getVert_succ_fin {x : V} (p : M.IndexedWalk x x) (hne : p.edges ≠ [])
    (i : Fin p.edges.length) :
    p.toWalk.getVert (i.val + 1) =
      p.toWalk.getVert (cyclicNext p.edges.length (List.length_pos_of_ne_nil hne) i).val := by
  by_cases hlt : i.val + 1 < p.edges.length
  · simp [cyclicNext, Nat.mod_eq_of_lt hlt]
  · have heq : i.val + 1 = p.edges.length := by omega
    have hlength : p.toWalk.length = p.edges.length := p.length_toWalk
    calc
      p.toWalk.getVert (i.val + 1) = x := by
        rw [heq, ← hlength, p.toWalk.getVert_length]
      _ = p.toWalk.getVert 0 := p.toWalk.getVert_zero.symm
      _ = p.toWalk.getVert
          (cyclicNext p.edges.length (List.length_pos_of_ne_nil hne) i).val := by
        congr 1
        simp [cyclicNext, heq]

end IndexedWalk
end EdgeIndexedMultigraph
end SimpleGraph
