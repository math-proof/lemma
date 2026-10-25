/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift.Part4
/-!
# Lifting partition congruences to mex partition functions

This file proves the Barman-Singh lift by removing the forced parts preceding a partition's
minimal excludant and then summing the resulting exact-mex fibers.
-/


namespace MetaMathlibExt

theorem mex_linear_target_iff {N A : ℕ} (hA : 0 < A) (p : Nat.Partition N) :
    (∃ μ, 0 < μ ∧ μ % A = A % A ∧ μ ∉ p.parts ∧
      (∀ k, 0 < k → k < μ → k % A = A % A → k ∈ p.parts) ∧
      μ % (2 * A) = A % (2 * A)) ↔
      Even (mex_index (mex_linear_candidate A) (mex_linear_candidate_strict A hA) p) := by
  exact mex_target_iff_even_index (mex_linear_candidate A)
    (mex_linear_candidate_strict A hA)
    (fun x => x % A = A % A) (fun x => x % (2 * A) = A % (2 * A))
    (fun x => mex_linear_candidate_iff A x hA)
    (fun j => mex_linear_selected_iff A j hA) p

theorem mex_odd_target_iff {N A : ℕ} (hA : 0 < A) (p : Nat.Partition N) :
    (∃ μ, 0 < μ ∧ μ % (2 * A) = A % (2 * A) ∧ μ ∉ p.parts ∧
      (∀ k, 0 < k → k < μ → k % (2 * A) = A % (2 * A) → k ∈ p.parts) ∧
      μ % (2 * (2 * A)) = A % (2 * (2 * A))) ↔
      Even (mex_index (mex_odd_candidate A) (mex_odd_candidate_strict A hA) p) := by
  exact mex_target_iff_even_index (mex_odd_candidate A)
    (mex_odd_candidate_strict A hA)
    (fun x => x % (2 * A) = A % (2 * A))
    (fun x => x % (2 * (2 * A)) = A % (2 * (2 * A)))
    (fun x => mex_odd_candidate_iff A x hA)
    (fun j => mex_odd_selected_iff A j hA) p

/-- Lifting of partition congruences to mex partition functions.

If `m ∣ p (a*n+b)` for all `n` (with `p` the ordinary partition number),
then for every `t ≥ 1` the same congruence holds for the mex partition
functions `p_{at,at}` and `p_{2at,at}`: `μ` encodes the `mex_{A,a}` value
(smallest positive integer `≡ a (mod A)` missing from the parts) and the
filter keeps partitions with `mex ≡ a (mod 2A)`. The offset `b` is taken in
`ℕ` with `b < a`, so `hbase` covers the whole residue class of `b` mod `a`;
for `b ≥ a` the lift needs `p` at arguments below `b`, which `hbase` does not
cover.

Source: Rupam Barman and Ajit Singh, "Mex-Related Partition Functions of
Andrews and Newman," Journal of Integer Sequences 24 (2021),
Article 21.6.3, Theorem (label thm2), lines 172–182,
https://cs.uwaterloo.ca/journals/JIS/VOL24/Barman/barman3.tex

This is the general lift; the same paper's Ramanujan corollary for
`p = 5, 7, 11` (label ramanujan-cong) is a separate module.

Proves `Wanted` entry `mesh_partition_congruence_lift`.

Proof: Following the Andrews-Newman mex decomposition used by Barman and Singh, remove one copy
of every forced earlier mex candidate. The exact-mex fibers then telescope, while every removed
prefix sum remains a multiple of `a`.
-/
theorem mesh_partition_congruence_lift
    (m a b : ℕ) (_hm : 0 < m) (ha : 0 < a) (hb : b < a)
    (hbase : ∀ n : ℕ, m ∣ Fintype.card (Nat.Partition (a * n + b))) :
    ∀ t : ℕ, 0 < t →
      (∀ n : ℕ, m ∣ (@Finset.filter (Nat.Partition (a * n + b))
        (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (a * t) = (a * t) % (a * t) ∧
          μ ∉ lam.parts ∧
          (∀ k : ℕ, 0 < k → k < μ → k % (a * t) = (a * t) % (a * t) →
            k ∈ lam.parts) ∧
          μ % (2 * (a * t)) = (a * t) % (2 * (a * t)))
        (Classical.decPred _) Finset.univ).card) ∧
      (∀ n : ℕ, m ∣ (@Finset.filter (Nat.Partition (a * n + b))
        (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (2 * a * t) = (a * t) % (2 * a * t) ∧
          μ ∉ lam.parts ∧
          (∀ k : ℕ, 0 < k → k < μ → k % (2 * a * t) = (a * t) % (2 * a * t) →
            k ∈ lam.parts) ∧
          μ % (2 * (2 * a * t)) = (a * t) % (2 * (2 * a * t)))
        (Classical.decPred _) Finset.univ).card) := by
  classical
  intro t ht
  have hA : 0 < a * t := Nat.mul_pos ha ht
  constructor
  · intro n
    have hc := mex_linear_candidate_strict (a * t) hA
    have hcpos := mex_linear_candidate_pos (a * t) hA
    have hsum : ∀ j,
        (mex_prefix (mex_linear_candidate (a * t)) j).sum =
          a * (t * ∑ i ∈ Finset.range j, (i + 1)) := by
      intro j
      change (mex_prefix (fun i => (a * t) * (i + 1)) j).sum = _
      exact mex_scaled_prefix_sum a t (fun i => i + 1)
        (by
          intro i k hik
          apply Nat.mul_lt_mul_of_pos_left _ hA
          omega) j
    have hdiv := mex_even_index_card_dvd m a b n hb hbase
      (mex_linear_candidate (a * t)) hc hcpos
      (fun j => t * ∑ i ∈ Finset.range j, (i + 1)) hsum
    have hfilter :
        (@Finset.filter (Nat.Partition (a * n + b))
          (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (a * t) = (a * t) % (a * t) ∧
            μ ∉ lam.parts ∧
            (∀ k : ℕ, 0 < k → k < μ → k % (a * t) = (a * t) % (a * t) →
              k ∈ lam.parts) ∧
            μ % (2 * (a * t)) = (a * t) % (2 * (a * t)))
          (Classical.decPred _) Finset.univ) =
          (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
            Even (mex_index (mex_linear_candidate (a * t)) hc p)) := by
      apply Finset.filter_congr
      intro p hp
      exact mex_linear_target_iff hA p
    rw [hfilter]
    exact hdiv
  · intro n
    have hc := mex_odd_candidate_strict (a * t) hA
    have hcpos := mex_odd_candidate_pos (a * t) hA
    have hsum : ∀ j,
        (mex_prefix (mex_odd_candidate (a * t)) j).sum =
          a * (t * ∑ i ∈ Finset.range j, (2 * i + 1)) := by
      intro j
      change (mex_prefix (fun i => (a * t) * (2 * i + 1)) j).sum = _
      exact mex_scaled_prefix_sum a t (fun i => 2 * i + 1)
        (by
          intro i k hik
          apply Nat.mul_lt_mul_of_pos_left _ hA
          omega) j
    have hdiv := mex_even_index_card_dvd m a b n hb hbase
      (mex_odd_candidate (a * t)) hc hcpos
      (fun j => t * ∑ i ∈ Finset.range j, (2 * i + 1)) hsum
    have hfilter :
        (@Finset.filter (Nat.Partition (a * n + b))
          (fun lam => ∃ μ : ℕ, 0 < μ ∧ μ % (2 * a * t) = (a * t) % (2 * a * t) ∧
            μ ∉ lam.parts ∧
            (∀ k : ℕ, 0 < k → k < μ → k % (2 * a * t) = (a * t) % (2 * a * t) →
              k ∈ lam.parts) ∧
            μ % (2 * (2 * a * t)) = (a * t) % (2 * (2 * a * t)))
          (Classical.decPred _) Finset.univ) =
          (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
            Even (mex_index (mex_odd_candidate (a * t)) hc p)) := by
      apply Finset.filter_congr
      intro p hp
      simpa only [mul_assoc] using mex_odd_target_iff hA p
    rw [hfilter]
    exact hdiv

end MetaMathlibExt
