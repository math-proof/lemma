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
import Structure.Combinatorics.SimpleGraph.FleischnerStrong.Part5
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

/-- Expand one compressed edge in front of an already expanded tail. -/
def prependExpandedTransition [DecidableEq V] {T : Type*}
    (transition : T → M.EdgeTransition) {a b c : V}
    (e : M.CompressedTransitionEdge transition)
    (he : (M.compressTransitions transition).ends e = s(a, b))
    (q : M.IndexedWalk b c) : M.PrependedTransition transition e he q := by
  cases e with
  | inl e =>
      exact ⟨.cons e.1 he q, List.Perm.refl _, rfl⟩
  | inr t =>
      change s((transition t).before, (transition t).after) = s(a, b) at he
      by_cases ha : a = (transition t).before
      · subst a
        have hb : b = (transition t).after := by
          rcases Sym2.eq_iff.mp he with h | h
          · exact h.2.symm
          · exact False.elim ((transition t).before_ne_after h.2.symm)
        subst b
        exact ⟨.cons (transition t).left (transition t).left_ends
          (.cons (transition t).right (transition t).right_ends q),
          by simp [transitionExpansionEdges], Or.inl rfl⟩
      · have hab : a = (transition t).after ∧ b = (transition t).before := by
          rcases Sym2.eq_iff.mp he with h | h
          · exact False.elim (ha h.1.symm)
          · exact ⟨h.2.symm, h.1.symm⟩
        rcases hab with ⟨hafter, hbefore⟩
        subst a
        subst b
        refine ⟨.cons (transition t).right
          ((transition t).right_ends.trans Sym2.eq_swap)
          (.cons (transition t).left
            ((transition t).left_ends.trans Sym2.eq_swap) q), ?_, Or.inr rfl⟩
        exact List.Perm.swap (transition t).left (transition t).right q.edges

end EdgeIndexedMultigraph
end SimpleGraph
