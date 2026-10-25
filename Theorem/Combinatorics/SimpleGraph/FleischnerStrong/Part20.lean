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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part32
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

namespace CyclicCircuit

variable (C : M.CyclicCircuit)

theorem rotatedPositions_eq_cons_cons (start : Fin C.size)
    (hsize : 2 ≤ C.size) :
    ∃ l, C.rotatedPositions M start =
      start :: cyclicNext C.size C.size_pos start :: l := by
  have hlength : (C.rotatedPositions M start).length = C.size := by
    simp [rotatedPositions]
  have hget0 : (C.rotatedPositions M start)[0]? = some start := by
    change (List.ofFn fun i ↦ C.rotatedPosition M start i)[0]? = some start
    rw [List.getElem?_ofFn]
    simp only [dite_eq_left C.size_pos]
    congr 1
    apply Fin.ext
    simp [rotatedPosition, Fin.val_add, Nat.mod_eq_of_lt start.isLt]
  have hget1 : (C.rotatedPositions M start)[1]? =
      some (cyclicNext C.size C.size_pos start) := by
    change (List.ofFn fun i ↦ C.rotatedPosition M start i)[1]? = _
    rw [List.getElem?_ofFn]
    split
    · rename_i hone
      congr 1
    · omega
  cases hrot : C.rotatedPositions M start with
  | nil =>
      exfalso
      rw [hrot] at hlength
      simp at hlength
      omega
  | cons a l =>
      cases hl : l with
      | nil =>
          exfalso
          rw [hrot, hl] at hlength
          simp at hlength
          omega
      | cons b t =>
          rw [hrot, hl] at hget0 hget1
          have ha : a = start := by
            simpa only [List.getElem?_cons_zero, Option.some.injEq] using hget0
          have hb : b = cyclicNext C.size C.size_pos start := by
            simpa only [List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] using hget1
          rw [ha, hb]
          refine ⟨t, ?_⟩
          rfl

/-- Every vertex occurs in the noninitial part of the kept cyclic listing. -/
theorem mem_tail_keptVertexListing (start : Fin C.size)
    (marked : Fin C.size → Bool) (hstart : marked start = false)
    (hunique : ∀ z, ∃! i, C.vertex i = z ∧ marked i = false) (z : V) :
    z ∈ (C.keptVertexListing M start marked).tail := by
  obtain ⟨l, hl⟩ := C.keptCoreVertices_eq_cons M start marked hstart hunique
  have hz := C.mem_keptCoreVertices M start marked hunique z
  rw [keptVertexListing, hl, List.cons_append, List.tail_cons]
  by_cases hroot : z = C.vertex start
  · subst z
    simp
  · rw [hl, List.mem_cons] at hz
    exact List.mem_append_left _ (hz.resolve_left hroot)

end CyclicCircuit
end EdgeIndexedMultigraph
end SimpleGraph
