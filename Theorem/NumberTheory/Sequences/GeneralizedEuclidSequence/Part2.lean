/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/GeneralizedEuclidSequence.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Associated
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.List.GetD
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.RingTheory.ZMod.UnitsCyclic
import Mathlib.Algebra.Pointwise.Stabilizer
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Factors
import Mathlib.GroupTheory.GroupAction.Quotient
import Def.NumberTheory.Sequences.GeneralizedEuclidSequence.Part2
/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/


namespace MetaMathlibExt

open scoped Pointwise

theorem geneuclid_odd_half_ge_two {p k : ℕ} (hp : 2 ≤ p) (hp3 : p ≠ 3)
    (hk : p = 2 * k + 1) : 2 ≤ k := by
  omega

theorem geneuclidBad_subset_square_multiples (N : ℕ) :
    geneuclidBad N ⊆ geneuclidMultiples N 4 ∪
      (geneuclidMultiples N 9 ∪ (Finset.range N).biUnion fun j =>
        geneuclidMultiples N ((2 * (j + 2) + 1) ^ 2)) := by
  intro e he
  rw [geneuclidBad, Finset.mem_filter] at he
  obtain ⟨p, hp, hpdvd⟩ := geneuclid_not_squarefree_exists_sq_dvd he.2
  have hsquare_le : p * p ≤ e + 1 := Nat.le_of_dvd (by omega) hpdvd
  have heN : e + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp he.1)
  have hp_le_square : p ≤ p * p := by
    nth_rewrite 1 [← Nat.mul_one p]
    exact Nat.mul_le_mul_left p hp.one_le
  have hpN : p ≤ N := hp_le_square.trans (hsquare_le.trans heN)
  rw [Finset.mem_union]
  by_cases hp2 : p = 2
  · left
    subst p
    exact Finset.mem_filter.mpr ⟨he.1, by norm_num at hpdvd ⊢; exact hpdvd⟩
  · right
    rw [Finset.mem_union]
    by_cases hp3 : p = 3
    · left
      subst p
      exact Finset.mem_filter.mpr ⟨he.1, by norm_num at hpdvd ⊢; exact hpdvd⟩
    · right
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      rw [Finset.mem_biUnion]
      have hjN : k - 2 < N := by omega
      refine ⟨k - 2, Finset.mem_range.mpr hjN, ?_⟩
      rw [geneuclidMultiples, Finset.mem_filter]
      refine ⟨he.1, ?_⟩
      have hk2 : 2 ≤ k := geneuclid_odd_half_ge_two hp.two_le hp3 hk
      have hbase : 2 * (k - 2 + 2) + 1 = p := by
        rw [Nat.sub_add_cancel hk2, hk]
      simpa [pow_two, hbase] using hpdvd

theorem geneuclidBad_card_le (N : ℕ) :
    (geneuclidBad N).card ≤ N / 4 + N / 9 +
      ∑ j ∈ Finset.range N, N / (2 * (j + 2) + 1) ^ 2 := by
  let A := geneuclidMultiples N 4
  let B := geneuclidMultiples N 9
  let C := (Finset.range N).biUnion fun j =>
    geneuclidMultiples N ((2 * (j + 2) + 1) ^ 2)
  have hsub : geneuclidBad N ⊆ A ∪ (B ∪ C) := geneuclidBad_subset_square_multiples N
  have hC : C.card ≤ ∑ j ∈ Finset.range N,
      (geneuclidMultiples N ((2 * (j + 2) + 1) ^ 2)).card :=
    Finset.card_biUnion_le
  calc
    (geneuclidBad N).card ≤ (A ∪ (B ∪ C)).card := Finset.card_le_card hsub
    _ ≤ A.card + (B ∪ C).card := Finset.card_union_le A (B ∪ C)
    _ ≤ A.card + (B.card + C.card) :=
      Nat.add_le_add_left (Finset.card_union_le B C) A.card
    _ ≤ A.card + (B.card + ∑ j ∈ Finset.range N,
        (geneuclidMultiples N ((2 * (j + 2) + 1) ^ 2)).card) :=
      Nat.add_le_add_left (Nat.add_le_add_left hC B.card) A.card
    _ = N / 4 + N / 9 + ∑ j ∈ Finset.range N, N / (2 * (j + 2) + 1) ^ 2 := by
      simp only [A, B, geneuclidMultiples, Nat.card_multiples]
      omega

theorem geneuclidBad_cast_le (N : ℕ) :
    ((geneuclidBad N).card : ℚ) ≤
      (N : ℚ) * ((1 / 4 : ℚ) + 1 / 9 + 1 / 8) := by
  have hbad : ((geneuclidBad N).card : ℚ) ≤
      ((N / 4 + N / 9 + ∑ j ∈ Finset.range N,
        N / (2 * (j + 2) + 1) ^ 2 : ℕ) : ℚ) := by
    exact_mod_cast geneuclidBad_card_le N
  have h4 : ((N / 4 : ℕ) : ℚ) ≤ (N : ℚ) / 4 := Nat.cast_div_le
  have h9 : ((N / 9 : ℕ) : ℚ) ≤ (N : ℚ) / 9 := Nat.cast_div_le
  have hsum : (∑ j ∈ Finset.range N,
      ((N / (2 * (j + 2) + 1) ^ 2 : ℕ) : ℚ)) ≤
      (N : ℚ) * (1 / 8) := by
    calc
      _ ≤ ∑ j ∈ Finset.range N,
          (N : ℚ) / (((2 * (j + 2) + 1 : ℕ) : ℚ) ^ 2) := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          ((N / (2 * (j + 2) + 1) ^ 2 : ℕ) : ℚ) ≤
              (N : ℚ) / (((2 * (j + 2) + 1) ^ 2 : ℕ) : ℚ) := Nat.cast_div_le
          _ = (N : ℚ) / (((2 * (j + 2) + 1 : ℕ) : ℚ) ^ 2) := by
            rw [Nat.cast_pow]
      _ = (N : ℚ) * ∑ j ∈ Finset.range N,
          (1 : ℚ) / (((2 * (j + 2) + 1 : ℕ) : ℚ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        field_simp
      _ ≤ (N : ℚ) * (1 / 8) := by
        exact mul_le_mul_of_nonneg_left (geneuclid_odd_sq_sum_le N) (by positivity)
  calc
    _ ≤ ((N / 4 : ℕ) : ℚ) + ((N / 9 : ℕ) : ℚ) +
        ∑ j ∈ Finset.range N, ((N / (2 * (j + 2) + 1) ^ 2 : ℕ) : ℚ) := by
      simpa only [Nat.cast_add, Nat.cast_sum] using hbad
    _ ≤ (N : ℚ) / 4 + (N : ℚ) / 9 + (N : ℚ) * (1 / 8) :=
      add_le_add (add_le_add h4 h9) hsum
    _ = (N : ℚ) * ((1 / 4 : ℚ) + 1 / 9 + 1 / 8) := by ring

theorem geneuclid_squarefree_majority (N : ℕ) (hN : 0 < N) :
    N < 2 * ((Finset.range N).filter fun e => Squarefree (e + 1)).card := by
  let good := (Finset.range N).filter fun e => Squarefree (e + 1)
  have hgood : good ⊆ Finset.range N := Finset.filter_subset _ _
  have hbad_eq : geneuclidBad N = Finset.range N \ good := by
    ext e
    simp [geneuclidBad, good]
    aesop
  have hcards : (geneuclidBad N).card + good.card = N := by
    have hgoodcard : good.card ≤ N := by simpa using Finset.card_le_card hgood
    rw [hbad_eq, Finset.card_sdiff_of_subset hgood, Finset.card_range]
    omega
  have hcoef : ((1 / 4 : ℚ) + 1 / 9 + 1 / 8) < 1 / 2 := by norm_num
  have hNq : (0 : ℚ) < N := by exact_mod_cast hN
  have hbad_lt : ((geneuclidBad N).card : ℚ) < (N : ℚ) * (1 / 2) :=
    (geneuclidBad_cast_le N).trans_lt (mul_lt_mul_of_pos_left hcoef hNq)
  have hbad_nat : 2 * (geneuclidBad N).card < N := by
    have hbad_lt' : (2 * (geneuclidBad N).card : ℚ) < N := by
      norm_num at hbad_lt ⊢
      linarith
    exact_mod_cast hbad_lt'
  change N < 2 * good.card
  omega

theorem geneuclid_squarefree_mem_units_of_primeFactors (q : ℕ) [Fact q.Prime]
    [NeZero q] (l : List ℕ) (hmin : ∀ p, p.Prime → p < q → p ∈ l) (d : ℕ)
    (hd0 : (d : ZMod q) ≠ 0) (hdsq : Squarefree d)
    (hfac : ∀ p ∈ d.primeFactors, p < q) :
    Units.mk0 (d : ZMod q) hd0 ∈ geneuclidUnits q l := by
  rw [mem_geneuclidUnits_iff]
  apply (mem_geneuclidResidues_iff q l _).mpr
  let I := d.primeFactors.image fun p => l.idxOf p
  have hmem (p : ℕ) (hp : p ∈ d.primeFactors) : p ∈ l := by
    have hpprime := Nat.prime_of_mem_primeFactors hp
    exact hmin p hpprime (hfac p hp)
  have hI : I ⊆ Finset.range l.length := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (List.idxOf_lt_length_iff.mpr (hmem p hp))
  refine ⟨I, hI, ?_⟩
  change (d : ZMod q) = ∏ i ∈ I, (eVal l i : ZMod q)
  have hinj : Set.InjOn (fun p => l.idxOf p) d.primeFactors := by
    intro p hp r hr hpr
    exact (List.idxOf_inj (hmem p hp)).mp hpr
  simp only [I]
  rw [Finset.prod_image hinj]
  have heval : ∀ p ∈ d.primeFactors, eVal l (l.idxOf p) = p := by
    intro p hp
    rw [eVal_lt l (l.idxOf p) (List.idxOf_lt_length_iff.mpr (hmem p hp))]
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (hmem p hp))
  rw [Finset.prod_congr rfl fun p hp => congrArg (fun n : ℕ => (n : ZMod q)) (heval p hp)]
  simpa only [Nat.cast_prod] using congrArg (fun n : ℕ => (n : ZMod q))
    (Nat.prod_primeFactors_of_squarefree hdsq).symm

theorem geneuclid_squarefree_mem_units (q : ℕ) [Fact q.Prime] [NeZero q]
    (l : List ℕ) (hmin : ∀ p, p.Prime → p < q → p ∈ l) (d : ℕ)
    (hdpos : 0 < d) (hdlt : d < q) (hdsq : Squarefree d) :
    Units.mk0 (d : ZMod q) (by
      intro hd0
      have hqd : q ∣ d := (ZMod.natCast_eq_zero_iff d q).mp hd0
      exact (not_le_of_gt hdlt) (Nat.le_of_dvd hdpos hqd)) ∈ geneuclidUnits q l := by
  apply geneuclid_squarefree_mem_units_of_primeFactors q l hmin d
  · exact hdsq
  · intro p hp
    exact (Nat.le_of_dvd hdpos (Nat.dvd_of_mem_primeFactors hp)).trans_lt hdlt

end MetaMathlibExt
