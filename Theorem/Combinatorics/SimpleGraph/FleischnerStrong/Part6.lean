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
public import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part10


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
theorem cyclicPrefix_zero {n : ℕ} [NeZero n] (d : Fin n → ℕ) :
    cyclicPrefix d 0 = 0 := by
  simp [cyclicPrefix]

theorem cyclicPrefix_eq_sub_one_add {n : ℕ} [NeZero n]
    (d : Fin n → ℕ) (i : Fin n) (hi : i ≠ 0) :
    cyclicPrefix d i = cyclicPrefix d (i - 1) + d i := by
  rcases i with ⟨i, hiLt⟩
  cases i with
  | zero => exact (hi rfl).elim
  | succ k =>
      let p : Fin n := ⟨k, lt_trans (Nat.lt_succ_self k) hiLt⟩
      have hp : (⟨k + 1, hiLt⟩ - 1 : Fin n) = p := by
        apply Fin.ext
        rw [Fin.val_sub_one_of_ne_zero hi]
        change k + 1 - 1 = k
        omega
      rw [hp]
      simp only [cyclicPrefix, p, Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last]

theorem zero_add_cyclicPrefix_last {m : ℕ} (d : Fin (m + 1) → ℕ) :
    d 0 + cyclicPrefix d (Fin.last m) = ∑ i, d i := by
  rw [Fin.sum_univ_succ]
  simp only [cyclicPrefix, Fin.val_last]
  congr

