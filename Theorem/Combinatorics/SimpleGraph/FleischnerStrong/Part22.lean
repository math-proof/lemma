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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part34
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

/-- A split anchor never selects the distinguished edge when that edge carries a copy. -/
theorem splitCycleAnchorIndex_ne_cut {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (cut : ActiveCycleCopy q)
    (i : Fin n) : splitCycleAnchorIndex cut.1 i ≠ cut.1 := by
  have hcut0 := cut.ne_zero q
  by_cases hi : i = 0
  · simpa [splitCycleAnchorIndex, hi] using hcut0.symm
  · by_cases hik : i.val ≤ cut.1.val
    · intro h
      have hval := congrArg Fin.val h
      rw [splitCycleAnchorIndex, ite_eq_right hi, ite_eq_left hik,
        Fin.val_sub_one_of_ne_zero hi] at hval
      have hipos : 0 < i.val := Nat.pos_of_ne_zero (fun h ↦ hi (Fin.ext h))
      omega
    · intro h
      have hval := congrArg Fin.val h
      simp [splitCycleAnchorIndex, hi, hik] at hval
      omega

end Walk
end SimpleGraph
