/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/MexPartitionCongruenceLift.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.Partition.MexPartitionCongruenceLift.Part3
/-!
# Lifting partition congruences to mex partition functions

This file proves the Barman-Singh lift by removing the forced parts preceding a partition's
minimal excludant and then summing the resulting exact-mex fibers.
-/


namespace MetaMathlibExt

theorem mex_fiber_add_prefix_card {N : ℕ} (c : ℕ → ℕ)
    (hc : StrictMono c) (j : ℕ) :
    (Finset.univ.filter fun p : Nat.Partition N => mex_index c hc p = j).card +
        (Finset.univ.filter fun p : Nat.Partition N => mex_prefix c (j + 1) ≤ p.parts).card =
      (Finset.univ.filter fun p : Nat.Partition N => mex_prefix c j ≤ p.parts).card := by
  classical
  have hfiber :
      (Finset.univ.filter fun p : Nat.Partition N => mex_index c hc p = j) =
        (Finset.univ.filter fun p : Nat.Partition N => mex_prefix c j ≤ p.parts).filter
          fun p => c j ∉ p.parts := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mex_index_eq_iff c hc p j
  have hnext :
      (Finset.univ.filter fun p : Nat.Partition N => mex_prefix c (j + 1) ≤ p.parts) =
        (Finset.univ.filter fun p : Nat.Partition N => mex_prefix c j ≤ p.parts).filter
          fun p => c j ∈ p.parts := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact mex_prefix_succ_le_iff c j p
  rw [hfiber, hnext]
  simpa only [not_not] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter fun p : Nat.Partition N => mex_prefix c j ≤ p.parts)
      (fun p => c j ∉ p.parts))

theorem mex_fiber_card_dvd (m a b n : ℕ) (hb : b < a)
    (hbase : ∀ q : ℕ, m ∣ Fintype.card (Nat.Partition (a * q + b)))
    (c : ℕ → ℕ) (hc : StrictMono c) (hcpos : ∀ i, 0 < c i) (T : ℕ → ℕ)
    (hsum : ∀ j, (mex_prefix c j).sum = a * T j) (j : ℕ) :
    m ∣ (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
      mex_index c hc p = j).card := by
  have hprefix := mex_required_card_dvd m a b n (T j) hb hbase (mex_prefix c j)
    (mex_prefix_pos c hcpos j) (hsum j)
  have hnext := mex_required_card_dvd m a b n (T (j + 1)) hb hbase
    (mex_prefix c (j + 1)) (mex_prefix_pos c hcpos (j + 1)) (hsum (j + 1))
  have hadd : m ∣
      (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
        mex_index c hc p = j).card +
      (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
        mex_prefix c (j + 1) ≤ p.parts).card := by
    rw [mex_fiber_add_prefix_card c hc j]
    exact hprefix
  exact (Nat.dvd_add_iff_left hnext).mpr hadd

theorem mex_even_index_card_dvd (m a b n : ℕ) (hb : b < a)
    (hbase : ∀ q : ℕ, m ∣ Fintype.card (Nat.Partition (a * q + b)))
    (c : ℕ → ℕ) (hc : StrictMono c) (hcpos : ∀ i, 0 < c i) (T : ℕ → ℕ)
    (hsum : ∀ j, (mex_prefix c j).sum = a * T j) :
    m ∣ (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
      Even (mex_index c hc p)).card := by
  classical
  have hfilter :
      (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
        Even (mex_index c hc p)) =
      (Finset.univ.filter fun p : Nat.Partition (a * n + b) =>
        mex_index c hc p ∈ (Finset.range (a * n + b + 2)).filter Even) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · intro heven
      exact ⟨by have := mex_index_le c hc p; omega, heven⟩
    · rintro ⟨-, heven⟩
      exact heven
  have hfibers := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Nat.Partition (a * n + b)))
    ((Finset.range (a * n + b + 2)).filter Even) (mex_index c hc)
  rw [hfilter, ← hfibers]
  apply Finset.dvd_sum
  intro j hj
  exact mex_fiber_card_dvd m a b n hb hbase c hc hcpos T hsum j

theorem mex_target_iff_even_index {N : ℕ} (c : ℕ → ℕ)
    (hc : StrictMono c) (Q S : ℕ → Prop)
    (hQ : ∀ x, 0 < x ∧ Q x ↔ ∃ j, x = c j) (hS : ∀ j, S (c j) ↔ Even j)
    (p : Nat.Partition N) :
    (∃ μ, 0 < μ ∧ Q μ ∧ μ ∉ p.parts ∧
      (∀ k, 0 < k → k < μ → Q k → k ∈ p.parts) ∧ S μ) ↔
      Even (mex_index c hc p) := by
  constructor
  · rintro ⟨μ, hμpos, hQμ, hmissing, hbelow, hselected⟩
    obtain ⟨j, rfl⟩ := (hQ μ).mp ⟨hμpos, hQμ⟩
    have hle : mex_index c hc p ≤ j := by
      unfold mex_index
      exact Nat.find_min' (mex_exists_missing c hc p) hmissing
    have hge : j ≤ mex_index c hc p := by
      apply Nat.not_lt.mp
      intro hlt
      have hcand := (hQ _).mpr ⟨mex_index c hc p, rfl⟩
      have hmem := hbelow (c (mex_index c hc p)) hcand.1 (hc hlt) hcand.2
      exact (mex_index_not_mem c hc p) hmem
    have heq : mex_index c hc p = j := Nat.le_antisymm hle hge
    rw [heq]
    exact (hS j).mp hselected
  · intro heven
    have hcand := (hQ _).mpr ⟨mex_index c hc p, rfl⟩
    refine ⟨c (mex_index c hc p), hcand.1, hcand.2, mex_index_not_mem c hc p,
      ?_, (hS _).mpr heven⟩
    intro k hkpos hklt hkQ
    obtain ⟨i, rfl⟩ := (hQ k).mp ⟨hkpos, hkQ⟩
    exact mex_index_mem_of_lt c hc p ((hc.lt_iff_lt).mp hklt)

end MetaMathlibExt
