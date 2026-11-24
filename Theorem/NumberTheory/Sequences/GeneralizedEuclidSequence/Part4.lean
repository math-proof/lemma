module
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.List.GetD
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Tactic.FieldSimp
public import Mathlib.NumberTheory.JacobiSum.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.RingTheory.ZMod.UnitsCyclic
public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Data.Nat.Factors
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Def.NumberTheory.Sequences.GeneralizedEuclidSequence.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Sequences/GeneralizedEuclidSequence.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Generalized Euclid sequences contain every prime

This file proves that every finite prime seed extends to an injective generalized Euclid
sequence containing every prime.
-/
namespace MetaMathlibExt

open scoped Pointwise

theorem geneuclidThirteenRepresentatives_card :
    geneuclidThirteenRepresentatives.card = 12 := by
  decide

theorem geneuclid_prime_lt_seven_of_dvd_thirty {p : ℕ} (hp : p.Prime)
    (h : p ∣ 30) : p < 7 := by
  rw [show 30 = (2 * 3) * 5 by norm_num, hp.dvd_mul, hp.dvd_mul] at h
  rcases h with (h | h) | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h]
    norm_num

theorem geneuclid_prime_lt_thirteen_of_dvd_primorial {p : ℕ} (hp : p.Prime)
    (h : p ∣ 2310) : p < 13 := by
  rw [show 2310 = (((2 * 3) * 5) * 7) * 11 by norm_num,
    hp.dvd_mul, hp.dvd_mul, hp.dvd_mul, hp.dvd_mul] at h
  rcases h with (((h | h) | h) | h) | h
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h]
    norm_num
  · rw [(Nat.prime_dvd_prime_iff_eq hp Nat.prime_eleven).mp h]
    norm_num

theorem geneuclidSevenRepresentatives_subset [Fact (Nat.Prime 7)] [NeZero 7]
    (l : List ℕ) (hmin : ∀ p, p.Prime → p < 7 → p ∈ l) :
    geneuclidSevenRepresentatives ⊆ geneuclidUnits 7 l := by
  intro u hu
  simp only [geneuclidSevenRepresentatives, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl
  all_goals
    apply geneuclid_squarefree_mem_units_of_primeFactors 7 l hmin
    · apply geneuclid_squarefree_thirty.squarefree_of_dvd
      norm_num
    · intro p hp
      apply geneuclid_prime_lt_seven_of_dvd_thirty (Nat.prime_of_mem_primeFactors hp)
      exact (Nat.dvd_of_mem_primeFactors hp).trans (by norm_num)

theorem geneuclidThirteenRepresentatives_subset [Fact (Nat.Prime 13)] [NeZero 13]
    (l : List ℕ) (hmin : ∀ p, p.Prime → p < 13 → p ∈ l) :
    geneuclidThirteenRepresentatives ⊆ geneuclidUnits 13 l := by
  intro u hu
  simp only [geneuclidThirteenRepresentatives, Finset.mem_insert,
    Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply geneuclid_squarefree_mem_units_of_primeFactors 13 l hmin
    · apply geneuclid_squarefree_two_thousand_three_hundred_ten.squarefree_of_dvd
      norm_num
    · intro p hp
      apply geneuclid_prime_lt_thirteen_of_dvd_primorial
        (Nat.prime_of_mem_primeFactors hp)
      exact (Nat.dvd_of_mem_primeFactors hp).trans (by norm_num)

theorem geneuclidUnits_large (q : ℕ) [Fact q.Prime] [NeZero q]
    (hq2 : q ≠ 2) (l : List ℕ) (hmin : ∀ p, p.Prime → p < q → p ∈ l) :
    q - 1 < 2 * (geneuclidUnits q l).card := by
  let good := (Finset.range (q - 1)).filter fun e => Squarefree (e + 1)
  have hq3 : 3 ≤ q := by
    have hq := (Fact.out : q.Prime).two_le
    omega
  let f : {e // e ∈ good} → {u // u ∈ geneuclidUnits q l} := fun e =>
    let heRange : e.1 < q - 1 := Finset.mem_range.mp (Finset.mem_filter.mp e.2).1
    let hdlt : e.1 + 1 < q := by omega
    let hd0 : ((e.1 + 1 : ℕ) : ZMod q) ≠ 0 := by
      intro hz
      have hqd : q ∣ e.1 + 1 := (ZMod.natCast_eq_zero_iff (e.1 + 1) q).mp hz
      exact (not_le_of_gt hdlt) (Nat.le_of_dvd (by omega) hqd)
    ⟨Units.mk0 ((e.1 + 1 : ℕ) : ZMod q) hd0,
      geneuclid_squarefree_mem_units q l hmin (e.1 + 1) (by omega) hdlt
        (Finset.mem_filter.mp e.2).2⟩
  have hf : Function.Injective f := by
    intro e r her
    apply Subtype.ext
    have hval := congrArg Units.val (congrArg Subtype.val her)
    have heRange : e.1 < q - 1 := Finset.mem_range.mp (Finset.mem_filter.mp e.2).1
    have hrRange : r.1 < q - 1 := Finset.mem_range.mp (Finset.mem_filter.mp r.2).1
    have heq : e.1 + 1 < q := by omega
    have hrq : r.1 + 1 < q := by omega
    simp only [f, Units.val_mk0] at hval
    have hval' := congrArg ZMod.val hval
    rw [ZMod.val_natCast_of_lt heq, ZMod.val_natCast_of_lt hrq] at hval'
    omega
  have hcard : good.card ≤ (geneuclidUnits q l).card :=
    Finset.card_le_card_of_injective hf
  have hmajor := geneuclid_squarefree_majority (q - 1) (by omega)
  change q - 1 < 2 * good.card at hmajor
  omega

end MetaMathlibExt
