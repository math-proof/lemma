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
import Structure.Combinatorics.SimpleGraph.FleischnerStrong.Part8
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
