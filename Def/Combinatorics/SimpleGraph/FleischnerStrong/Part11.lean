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
public import Theorem.Combinatorics.SimpleGraph.FleischnerStrong.Part6


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

