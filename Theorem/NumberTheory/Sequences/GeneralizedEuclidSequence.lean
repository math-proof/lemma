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
import Def.NumberTheory.Sequences.GeneralizedEuclidSequence
/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/


namespace MetaMathlibExt

open scoped Pointwise

theorem mem_geneuclidUnits_iff (q : ℕ) [NeZero q] (l : List ℕ) (u : (ZMod q)ˣ) :
    u ∈ geneuclidUnits q l ↔ (u : ZMod q) ∈ geneuclidResidues q l := by
  simp [geneuclidUnits]

theorem mem_geneuclidResidues_iff (q : ℕ) (l : List ℕ) (x : ZMod q) :
    x ∈ geneuclidResidues q l ↔ ∃ I ⊆ Finset.range l.length,
      x = ∏ i ∈ I, (eVal l i : ZMod q) := by
  simp only [geneuclidResidues, Finset.mem_image, Finset.mem_powerset]
  aesop

theorem eVal_lt (l : List ℕ) (i : ℕ) (h : i < l.length) : eVal l i = l[i] :=
  List.getD_eq_getElem l 0 h

theorem geneuclidResidues_ne_zero (l : List ℕ) (hprime : ∀ p ∈ l, p.Prime)
    (q : ℕ) (hq : q.Prime) (hqnot : q ∉ l) {x : ZMod q}
    (hx : x ∈ geneuclidResidues q l) : x ≠ 0 := by
  let _ : Fact q.Prime := ⟨hq⟩
  obtain ⟨I, hI, rfl⟩ := (mem_geneuclidResidues_iff q l x).mp hx
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hil : i < l.length := Finset.mem_range.mp (hI hi)
  rw [eVal_lt l i hil]
  intro hz
  have hdiv : q ∣ l[i] := (ZMod.natCast_eq_zero_iff l[i] q).mp hz
  have heq : q = l[i] :=
    (Nat.prime_dvd_prime_iff_eq hq (hprime l[i] (List.getElem_mem hil))).mp hdiv
  exact hqnot (heq ▸ List.getElem_mem hil)

theorem eVal_prefix (l l' : List ℕ) (h : l <+: l') (i : ℕ) (hi : i < l.length) :
    eVal l i = eVal l' i := by
  unfold eVal
  rw [List.prefix_iff_eq_append] at h
  rw [← h]
  exact (List.getD_append l (List.drop l.length l') 0 i hi).symm

theorem geneuclidResidues_append_subset (q : ℕ) (l : List ℕ) (r : ℕ) :
    geneuclidResidues q l ⊆ geneuclidResidues q (l ++ [r]) := by
  intro x hx
  obtain ⟨I, hI, rfl⟩ := (mem_geneuclidResidues_iff q l x).mp hx
  apply (mem_geneuclidResidues_iff q (l ++ [r]) _).mpr
  refine ⟨I, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_range, List.length_append, List.length_singleton]
    exact Nat.lt_succ_of_lt (Finset.mem_range.mp (hI hi))
  · apply Finset.prod_congr rfl
    intro i hi
    rw [eVal_prefix l (l ++ [r]) (List.prefix_append l [r]) i
      (Finset.mem_range.mp (hI hi))]

theorem geneuclidUnits_append_subset (q : ℕ) [NeZero q] (l : List ℕ) (r : ℕ) :
    geneuclidUnits q l ⊆ geneuclidUnits q (l ++ [r]) := by
  intro u hu
  rw [mem_geneuclidUnits_iff] at hu ⊢
  exact geneuclidResidues_append_subset q l r hu

theorem geneuclidUnits_mul_mk0_mem_append (q : ℕ) [Fact q.Prime] [NeZero q]
    (l : List ℕ)
    (r : ℕ) (hr : (r : ZMod q) ≠ 0) (u : (ZMod q)ˣ) (hu : u ∈ geneuclidUnits q l) :
    u * Units.mk0 (r : ZMod q) hr ∈ geneuclidUnits q (l ++ [r]) := by
  rw [mem_geneuclidUnits_iff] at hu ⊢
  obtain ⟨I, hI, huI⟩ := (mem_geneuclidResidues_iff q l u).mp hu
  apply (mem_geneuclidResidues_iff q (l ++ [r]) _).mpr
  have hlast : l.length < (l ++ [r]).length := by simp
  have hnot : l.length ∉ I := fun h => (Finset.mem_range.mp (hI h)).false
  have hevalLast : eVal (l ++ [r]) l.length = r := by
    rw [eVal_lt _ _ hlast]
    simp
  have hprod : (∏ i ∈ I, (eVal (l ++ [r]) i : ZMod q)) =
      ∏ i ∈ I, (eVal l i : ZMod q) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [← eVal_prefix l (l ++ [r]) (List.prefix_append l [r]) i
      (Finset.mem_range.mp (hI hi))]
  refine ⟨insert l.length I, ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_range]
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hlast
    · exact (Finset.mem_range.mp (hI hi)).trans hlast
  · rw [Finset.prod_insert hnot, hevalLast]
    change (u : ZMod q) * r = r * ∏ i ∈ I, (eVal (l ++ [r]) i : ZMod q)
    rw [huI, hprod, mul_comm]

theorem geneuclidProduct_split (l : List ℕ) (I : Finset ℕ)
    (hI : I ⊆ Finset.range l.length) :
    geneuclidProduct l =
      (∏ i ∈ I, eVal l i) * ∏ i ∈ (Finset.range l.length \ I), eVal l i := by
  rw [geneuclidProduct, ← Finset.prod_sdiff hI, mul_comm]

theorem geneuclidProduct_append (l : List ℕ) (r : ℕ) :
    geneuclidProduct (l ++ [r]) = geneuclidProduct l * r := by
  rw [geneuclidProduct, List.length_append, List.length_singleton, Finset.prod_range_succ]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    exact (eVal_prefix l (l ++ [r]) (List.prefix_append l [r]) i hi).symm
  · simp [eVal_lt]

theorem geneuclid_unit_expression (q : ℕ) [Fact q.Prime] [NeZero q]
    (l : List ℕ) (u : (ZMod q)ˣ) (hu : u ∈ geneuclidUnits q l) :
    ∃ I ⊆ Finset.range l.length,
      (u : ZMod q) + (geneuclidProduct l : ZMod q) / (u : ZMod q) =
        (geneuclidN l I : ℕ) := by
  rw [mem_geneuclidUnits_iff] at hu
  obtain ⟨I, hI, huI⟩ := (mem_geneuclidResidues_iff q l u).mp hu
  refine ⟨I, hI, ?_⟩
  let A := ∏ i ∈ I, eVal l i
  let B := ∏ i ∈ (Finset.range l.length \ I), eVal l i
  have huA : (u : ZMod q) = (A : ZMod q) := by
    simpa [A] using huI
  have hA : (A : ZMod q) ≠ 0 := by
    rw [← huA]
    exact u.ne_zero
  have hprod : geneuclidProduct l = A * B := geneuclidProduct_split l I hI
  change (u : ZMod q) + (geneuclidProduct l : ZMod q) / (u : ZMod q) =
    ((A + B : ℕ) : ZMod q)
  rw [huA, hprod, Nat.cast_mul, mul_div_cancel_left₀ _ hA, Nat.cast_add]

theorem geneuclid_q_appendable_iff_expression_zero (q : ℕ) [Fact q.Prime]
    [NeZero q] (l : List ℕ) (hprime : ∀ p ∈ l, p.Prime) (hqnot : q ∉ l) :
    GeneuclidAppendable l q ↔ ∃ u ∈ geneuclidUnits q l,
      (u : ZMod q) + (geneuclidProduct l : ZMod q) / (u : ZMod q) = 0 := by
  constructor
  · rintro ⟨_hq, I, hI, hdiv⟩
    let A := ∏ i ∈ I, eVal l i
    have hA0 : (A : ZMod q) ≠ 0 := by
      apply geneuclidResidues_ne_zero l hprime q Fact.out hqnot
      apply (mem_geneuclidResidues_iff q l _).mpr
      refine ⟨I, hI, ?_⟩
      simp [A]
    let u := Units.mk0 (A : ZMod q) hA0
    have hu : u ∈ geneuclidUnits q l := by
      rw [mem_geneuclidUnits_iff]
      apply (mem_geneuclidResidues_iff q l _).mpr
      refine ⟨I, hI, ?_⟩
      simp [u, A]
    refine ⟨u, hu, ?_⟩
    have hcast : (geneuclidN l I : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff (geneuclidN l I) q).mpr hdiv
    let B := ∏ i ∈ (Finset.range l.length \ I), eVal l i
    have hprod : geneuclidProduct l = A * B := geneuclidProduct_split l I hI
    change (A : ZMod q) + (geneuclidProduct l : ZMod q) / (A : ZMod q) = 0
    rw [hprod, Nat.cast_mul, mul_div_cancel_left₀ _ hA0, ← Nat.cast_add,
      show A + B = geneuclidN l I by rfl, hcast]
  · rintro ⟨u, hu, hzero⟩
    obtain ⟨I, hI, hExpr⟩ := geneuclid_unit_expression q l u hu
    refine ⟨Fact.out, I, hI, ?_⟩
    apply (ZMod.natCast_eq_zero_iff (geneuclidN l I) q).mp
    rw [← hExpr, hzero]

theorem geneuclid_not_squarefree_exists_sq_dvd {m : ℕ} (hm : ¬Squarefree m) :
    ∃ p, p.Prime ∧ p * p ∣ m := by
  rw [Nat.squarefree_iff_prime_squarefree] at hm
  push Not at hm
  obtain ⟨p, hp, hpdvd⟩ := hm
  exact ⟨p, hp, hpdvd⟩

theorem geneuclid_odd_sq_recip_le (k : ℕ) (hk : 2 ≤ k) :
    (1 : ℚ) / ((2 * k + 1 : ℕ) : ℚ) ^ 2 ≤
      (1 / 4 : ℚ) * (1 / (k : ℚ) - 1 / ((k + 1 : ℕ) : ℚ)) := by
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hk)
  have hk10 : (0 : ℚ) < k + 1 := by positivity
  have hodd0 : (0 : ℚ) < 2 * k + 1 := by positivity
  norm_num [Nat.cast_add, Nat.cast_mul] at *
  field_simp
  nlinarith

theorem geneuclid_recip_telescope (M : ℕ) :
    (∑ k ∈ Finset.range M,
      ((1 : ℚ) / ((k + 2 : ℕ) : ℚ) - 1 / ((k + 3 : ℕ) : ℚ))) =
        1 / 2 - 1 / ((M + 2 : ℕ) : ℚ) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      norm_num [Nat.cast_add, Nat.cast_succ]

theorem geneuclid_odd_sq_sum_le (M : ℕ) :
    (∑ k ∈ Finset.range M, (1 : ℚ) / ((2 * (k + 2) + 1 : ℕ) : ℚ) ^ 2) ≤ 1 / 8 := by
  calc
    _ ≤ ∑ k ∈ Finset.range M, (1 / 4 : ℚ) *
        (1 / ((k + 2 : ℕ) : ℚ) - 1 / ((k + 3 : ℕ) : ℚ)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact geneuclid_odd_sq_recip_le (k + 2) (by omega)
    _ = (1 / 4 : ℚ) * (1 / 2 - 1 / ((M + 2 : ℕ) : ℚ)) := by
      rw [← Finset.mul_sum, geneuclid_recip_telescope]
    _ ≤ 1 / 8 := by
      have hden : (0 : ℚ) < ((M + 2 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < M + 2)
      have hinv : (0 : ℚ) ≤ 1 / ((M + 2 : ℕ) : ℚ) := (one_div_pos.mpr hden).le
      calc
        _ ≤ (1 / 4 : ℚ) * (1 / 2) :=
          mul_le_mul_of_nonneg_left (sub_le_self _ hinv) (by norm_num)
        _ = 1 / 8 := by norm_num

end MetaMathlibExt
