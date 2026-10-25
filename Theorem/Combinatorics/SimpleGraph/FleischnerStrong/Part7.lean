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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part12
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

theorem cycleCopyMultigraph_inc_getVert_iff {c : G.Walk x x}
    (hc : c.IsCycle) [NeZero c.length] {d : Fin c.length → ℕ}
    (q : CyclicParityCompletion d) (i : Fin c.length) (e : c.CycleCopyEdge q) :
    (c.cycleCopyMultigraph q).Inc (c.getVert i) e ↔
      e.1 = i ∨ e.1 = i - 1 := by
  change c.getVert i ∈ s(c.getVert e.1, c.getVert (e.1.val + 1)) ↔ _
  rw [hc.getVert_succ_eq_add_one]
  constructor
  · intro he
    rcases Sym2.mem_iff.mp he with he | he
    · exact Or.inl (hc.getVert_injective_fin he.symm)
    · have hi : i = e.1 + 1 := hc.getVert_injective_fin he
      exact Or.inr (eq_sub_iff_add_eq.mpr hi.symm)
  · rintro (rfl | he)
    · exact Sym2.mem_iff.mpr (Or.inl rfl)
    · apply Sym2.mem_iff.mpr
      right
      apply congrArg c.getVert
      rw [he, sub_add_cancel]

theorem no_cover_inc_bound_vertex [Finite V] (c : G.Walk x x)
    (cover : (D : c.outsideGraph.ConnectedComponent) → c.ComponentTrailCover D)
    (i : Fin c.length) (hbound : c.IsBoundVertex (c.getVert i))
    (D : c.outsideGraph.ConnectedComponent) (f : (cover D).Edge) :
    ¬(c.trailSystemMultigraph cover).Inc (c.getVert i) (Sum.inr ⟨D, f⟩) := by
  intro hinc
  obtain ⟨z, hzD, hzinc⟩ := (cover D).meets_component f
  have hzout : z ∉ c.support := c.componentVertices_subset_compl D hzD
  have hne : c.getVert i ≠ z := by
    intro h
    exact hzout (h ▸ c.getVert_mem_support i)
  change c.getVert i ∈ (cover D).multigraph.ends f at hinc
  have hends : (cover D).multigraph.ends f = s(c.getVert i, z) :=
    (Sym2.mem_and_mem_iff hne).mp ⟨hinc, hzinc⟩
  have hadj : G.Adj (c.getVert i) z :=
    (cover D).cycle_edge f _ _ hends (Or.inl (c.getVert_mem_support i))
  exact hzout (hbound.2 hadj)

end Walk
end SimpleGraph
