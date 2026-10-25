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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part19
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

theorem ParallelPair.mem_range_edge_iff {M : EdgeIndexedMultigraph V E}
    (p : M.ParallelPair) (e : E) :
    e ∈ Set.range p.edge ↔ e = p.first ∨ e = p.second := by
  constructor
  · rintro ⟨i, rfl⟩
    have hi : i = 0 ∨ i = 1 := by
      have hval : i.val = 0 ∨ i.val = 1 := by omega
      exact hval.imp Fin.ext Fin.ext
    rcases hi with rfl | rfl
    · exact Or.inl (by simp [ParallelPair.edge])
    · exact Or.inr (by simp [ParallelPair.edge])
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [ParallelPair.edge]⟩
    · exact ⟨1, by simp [ParallelPair.edge]⟩

end EdgeIndexedMultigraph
end SimpleGraph
