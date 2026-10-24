import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.CombinatorialOptimization.code.Matching.HopcroftKarp
open SimpleGraph


namespace SimpleGraph

/--
[HopcroftKarpExecution.shortestLen_strict_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/HopcroftKarp.lean)
-/
@[path]
lemma HopcroftKarpExecution.shortestLen_strict_mono
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {exec : HopcroftKarpExecution.{u, w} G}
  {i : Fin exec.numPhases}
-- given
  (hi : i.val + 1 < exec.numPhases) :
-- imply
  exec.shortestLen i < exec.shortestLen ⟨i.val + 1, hi⟩ := by
-- proof
  have h_inc := shortest_aug_path_length_strict_increase
    (exec.matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (exec.matching ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
    (exec.isMatching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)
    (exec.shortestLen i)
    (exec.shortestLen_spec i)
    (exec.paths i)
    (exec.paths_maximal i)
    (exec.isAugmentation i)
  have h_spec := exec.shortestLen_spec ⟨i.val + 1, hi⟩
  have heq : (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ : Fin (exec.numPhases + 1)) =
    ⟨i.val + 1, Nat.lt_succ_of_lt hi⟩ := by
    ext; rfl
  rw [heq] at h_inc
  rw [h_spec] at h_inc
  exact ENat.coe_lt_coe.mp h_inc

end SimpleGraph

namespace SimpleGraph

/--
[HopcroftKarpExecution.shortestLen_odd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/HopcroftKarp.lean)
-/
@[path]
lemma HopcroftKarpExecution.shortestLen_odd
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {exec : HopcroftKarpExecution.{u, w} G}
  {i : Fin exec.numPhases} :
-- imply
  Odd (exec.shortestLen i) := by
-- proof
  have hspec := exec.shortestLen_spec i
  have hne : (augPathLengths G (exec.matching ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩)).Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    unfold shortestAugPathLength at hspec
    rw [hempty, sInf_empty] at hspec
    exact absurd hspec (by simp [ENat.top_ne_coe])
  have hmem := csInf_mem hne
  unfold shortestAugPathLength at hspec
  rw [hspec] at hmem
  obtain ⟨u, v, p, haug, hlen⟩ := hmem
  have hodd := augmenting_path_odd_length haug
  rw [p.length_edges] at hodd
  have hlen_eq : p.length = exec.shortestLen i := by
    have := ENat.coe_inj.mp hlen
    exact this
  rwa [hlen_eq] at hodd

end SimpleGraph

namespace SimpleGraph

/--
[HopcroftKarpExecution.shortestLen_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/HopcroftKarp.lean)
-/
@[path]
lemma HopcroftKarpExecution.shortestLen_lower_bound
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {exec : HopcroftKarpExecution.{u, w} G}
  {i : Fin exec.numPhases} :
-- imply
  2 * i.val + 1 ≤ exec.shortestLen i := by
-- proof
  obtain ⟨k, hk⟩ := i
  induction k with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add]
    exact Odd.pos (exec.shortestLen_odd ⟨0, hk⟩)
  | succ j ih =>
    have hj_lt : j < exec.numPhases := Nat.lt_of_succ_lt hk
    have ih_applied := ih hj_lt
    have hmono := exec.shortestLen_strict_mono ⟨j, hj_lt⟩ hk
    have hodd_j := exec.shortestLen_odd ⟨j, hj_lt⟩
    have hodd_succ := exec.shortestLen_odd ⟨j + 1, hk⟩
    have hstep : exec.shortestLen ⟨j, hj_lt⟩ + 2 ≤ exec.shortestLen ⟨j + 1, hk⟩ := by
      have hm := hodd_j
      have hn := hodd_succ
      obtain ⟨a, ha⟩ := hm
      obtain ⟨b, hb⟩ := hn
      simp only [ha, hb] at hmono ⊢
      omega
    linarith

end SimpleGraph

namespace SimpleGraph

/--
[HopcroftKarpExecution.matching_size_growth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/HopcroftKarp.lean)
-/
@[path]
lemma HopcroftKarpExecution.matching_size_growth
  {V : Type u}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {exec : HopcroftKarpExecution.{u, w} G}
  {i j : ℕ}
-- given
  (hij : i ≤ j)
  (hj : j ≤ exec.numPhases) :
-- imply
  (exec.matching ⟨i, Nat.lt_succ_of_le (hij.trans hj)⟩).edgeSet.ncard + (j - i) ≤ (exec.matching ⟨j, Nat.lt_succ_of_le hj⟩).edgeSet.ncard := by
-- proof
  induction hij with
  | refl => simp
  | @step m him ih =>
    have hm_le : m ≤ exec.numPhases := Nat.le_of_succ_le hj
    have ih_applied := ih hm_le
    have hm_lt : m < exec.numPhases := Nat.lt_of_succ_le hj
    have hstep := exec.size_strictly_increases ⟨m, hm_lt⟩
    have heq1 : (exec.matching ⟨m, Nat.lt_succ_of_lt hm_lt⟩).edgeSet.ncard =
      (exec.matching ⟨m, Nat.lt_succ_of_le hm_le⟩).edgeSet.ncard := by congr 2
    have heq2 : (exec.matching ⟨m + 1, Nat.succ_lt_succ hm_lt⟩).edgeSet.ncard =
      (exec.matching ⟨m + 1, Nat.lt_succ_of_le hj⟩).edgeSet.ncard := by congr 2
    have heq3 : (exec.matching ⟨i, Nat.lt_succ_of_le (Nat.le_trans him hm_le)⟩).edgeSet.ncard =
      (exec.matching ⟨i, Nat.lt_succ_of_le (Nat.le_trans (Nat.le_succ_of_le him) hj)⟩).edgeSet.ncard := by
      congr 2
    rw [heq1, heq2] at hstep
    rw [heq3] at ih_applied
    have hi_le_m : i ≤ m := him
    have hsub : m + 1 - i = (m - i) + 1 := Nat.succ_sub hi_le_m
    linarith [hsub]

end SimpleGraph


-- created on 2026-10-23
