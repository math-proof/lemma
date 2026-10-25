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
import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part6
/-!
# The strengthened Fleischner theorem

This file proves the vertex-rooted form of Fleischner's theorem: the square has a Hamiltonian
cycle whose two edges at a prescribed vertex are edges of the original graph.

The proof-specific component, trail, transition, Euler-circuit, and marking constructions are
private to this module.
-/

/-! ## CycleComplement -/


/-- The canonical parity completion, obtained by taking prefix parities away from position
zero. -/
noncomputable def cyclicParityCompletion {n : ℕ} [NeZero n]
    (d : Fin n → ℕ) (hsum : Even (∑ i, d i)) : CyclicParityCompletion d where
  copies i := cyclicPrefix d i % 2
  copies_lt_two i := Nat.mod_lt _ (by omega)
  copies_zero := by simp [cyclicPrefix_zero]
  even_at := by
    intro i
    by_cases hi : i = 0
    · subst i
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
      have hprev : (0 - 1 : Fin (m + 1)) = Fin.last m := by
        cases m with
        | zero =>
            apply Fin.ext
            rfl
        | succ k =>
            apply Fin.ext
            simp
      rw [hprev, cyclicPrefix_zero]
      rw [← zero_add_cyclicPrefix_last d] at hsum
      rw [Nat.even_iff] at hsum ⊢
      omega
    · rw [cyclicPrefix_eq_sub_one_add d i hi, Nat.even_iff]
      omega

