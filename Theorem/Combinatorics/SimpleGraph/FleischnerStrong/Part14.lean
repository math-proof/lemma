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
import Def.Combinatorics.SimpleGraph.FleischnerStrong.Part26
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

theorem splitPartnerIndex_val_on_active {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) (i : ActiveCycleCopy q) :
    (splitPartnerIndex k i.1).val =
      if i.1.val < k.val then i.1.val - 1 else i.1.val + 1 := by
  by_cases h : i.1.val < k.val
  · rw [splitPartnerIndex, ite_eq_left h, ite_eq_left h,
      Fin.val_sub_one_of_ne_zero (i.ne_zero q)]
  · have hiend := i.val_add_one_lt q hlast
    have hn2 : 1 < n :=
      lt_of_le_of_lt (Nat.succ_le_succ (Nat.zero_le i.1.val)) hiend
    have hone : (1 : Fin n).val = 1 := Nat.mod_eq_of_lt hn2
    have hadd : i.1.val + (1 : Fin n).val < n := by
      rw [hone]
      exact hiend
    rw [splitPartnerIndex, ite_eq_right h, ite_eq_right h]
    exact (Fin.val_add_eq_of_add_lt hadd).trans (by rw [hone])

theorem splitPartnerIndex_injective_on_active {n : ℕ} [NeZero n]
    {d : Fin n → ℕ} (q : CyclicParityCompletion d) (k : Fin n)
    (hlast : q.copies (cycleLastIndex n) = 0) :
    Function.Injective
      (fun i : ActiveCycleCopy q ↦ splitPartnerIndex k i.1) := by
  intro i j hij
  have hipos : 0 < i.1.val := by
    have hi0 := i.ne_zero q
    exact Nat.pos_of_ne_zero (fun h ↦ hi0 (Fin.ext h))
  have hjpos : 0 < j.1.val := by
    have hj0 := j.ne_zero q
    exact Nat.pos_of_ne_zero (fun h ↦ hj0 (Fin.ext h))
  apply Subtype.ext
  apply Fin.ext
  have hval := congrArg Fin.val hij
  change (splitPartnerIndex k i.1).val = (splitPartnerIndex k j.1).val at hval
  have hvali := splitPartnerIndex_val_on_active q k hlast i
  have hvalj := splitPartnerIndex_val_on_active q k hlast j
  have heq : (if i.1.val < k.val then i.1.val - 1 else i.1.val + 1) =
      if j.1.val < k.val then j.1.val - 1 else j.1.val + 1 :=
    hvali.symm.trans (hval.trans hvalj)
  by_cases hiklt : i.1.val < k.val <;> by_cases hjklt : j.1.val < k.val
  · simp [hiklt, hjklt] at heq
    omega
  · simp [hiklt, hjklt] at heq
    omega
  · simp [hiklt, hjklt] at heq
    omega
  · simp [hiklt, hjklt] at heq
    omega

end Walk
end SimpleGraph
