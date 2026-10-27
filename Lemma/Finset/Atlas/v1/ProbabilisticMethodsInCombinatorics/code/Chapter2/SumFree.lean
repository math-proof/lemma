import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.SumFree
open Finset SumFree


namespace SumFree

/--
[middleThird_sumFree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/SumFree.lean)
-/
@[path]
lemma middleThird_sumFree
  {p : ℕ}
  [NeZero p]
  {a b : ZMod p}
-- given
  (hp3 : p % 3 = 2)
  (hp2 : 2 < p)
  (ha1 : p / 3 < ZMod.val a)
  (ha2 : ZMod.val a ≤ 2 * p / 3)
  (hb1 : p / 3 < ZMod.val b)
  (hb2 : ZMod.val b ≤ 2 * p / 3) :
-- imply
  ¬(p / 3 < ZMod.val (a + b) ∧ ZMod.val (a + b) ≤ 2 * p / 3) := by
-- proof
  rw [ZMod.val_add]
  have hav := ZMod.val_lt a
  have hbv := ZMod.val_lt b
  obtain ⟨m, hm⟩ : ∃ m, p = 3 * m + 2 := ⟨p / 3, by omega⟩
  subst hm
  have hpd : (3 * m + 2) / 3 = m := by omega
  have h2pd : 2 * (3 * m + 2) / 3 = 2 * m + 1 := by omega
  simp only [hpd, h2pd] at ha1 ha2 hb1 hb2 ⊢
  intro ⟨h1, h2⟩
  by_cases hc : a.val + b.val < 3 * m + 2
  · have hmod : (a.val + b.val) % (3 * m + 2) = a.val + b.val := Nat.mod_eq_of_lt hc
    rw [hmod] at h1 h2; omega
  · have hge : 3 * m + 2 ≤ a.val + b.val := by omega
    have hmod : (a.val + b.val) % (3 * m + 2) = a.val + b.val - (3 * m + 2) := by
      rw [Nat.mod_eq_sub_mod hge]; exact Nat.mod_eq_of_lt (by omega)
    rw [hmod] at h1 h2; omega

end SumFree

namespace SumFree

/--
[card_filter_mul_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/SumFree.lean)
-/
@[path]
lemma card_filter_mul_right
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a : ZMod p}
  {B : Finset (ZMod p)}
-- given
  (ha : a ≠ 0) :
-- imply
  (Finset.univ.filter (fun t : ZMod p => t * a ∈ B)).card = B.card := by
-- proof
  rw [show (Finset.univ.filter (fun t : ZMod p => t * a ∈ B)) =
    B.map ⟨(· * a⁻¹), mul_left_injective₀ (inv_ne_zero ha)⟩ from by
    ext t
    simp only [mem_filter, mem_univ, true_and, mem_map, Function.Embedding.coeFn_mk]
    constructor
    · intro ht; exact ⟨t * a, ht, by rw [mul_assoc, mul_inv_cancel₀ ha, mul_one]⟩
    · intro ⟨y, hy, hyt⟩; rw [← hyt, mul_assoc, inv_mul_cancel₀ ha, mul_one]; exact hy]
  exact Finset.card_map _

end SumFree

namespace SumFree

/--
[card_filter_val_Ioc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/SumFree.lean)
-/
@[path]
lemma card_filter_val_Ioc
  {p : ℕ}
  [NeZero p]
  {a b : ℕ}
-- given
  (hb : b < p) :
-- imply
  (Finset.univ.filter (fun x : ZMod p => a < ZMod.val x ∧ ZMod.val x ≤ b)).card = b - a := by
-- proof
  have key : (Finset.univ.filter (fun x : ZMod p => a < ZMod.val x ∧ ZMod.val x ≤ b)) =
    ((Finset.Ioc a b).image (fun n : ℕ => (n : ZMod p))) := by
    ext x
    simp only [mem_filter, mem_univ, true_and, mem_image, Finset.mem_Ioc]
    exact ⟨fun ⟨h1, h2⟩ => ⟨ZMod.val x, ⟨h1, h2⟩, ZMod.natCast_zmod_val x⟩,
      fun ⟨n, ⟨hn1, hn2⟩, hnx⟩ => by
        rw [← hnx, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : n < p)]; exact ⟨hn1, hn2⟩⟩
  rw [key, Finset.card_image_of_injOn (fun x hx y hy hxy => by
    have hxm := (Finset.mem_Ioc.mp hx).2
    have hym := (Finset.mem_Ioc.mp hy).2
    have h := congr_arg ZMod.val hxy
    rwa [ZMod.val_natCast, ZMod.val_natCast,
      Nat.mod_eq_of_lt (show x < p by omega), Nat.mod_eq_of_lt (show y < p by omega)] at h)]
  exact Nat.card_Ioc a b

end SumFree

namespace SumFree

/--
[double_count](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/SumFree.lean)
-/
@[path]
lemma double_count
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {A : Finset ℤ}
  {B : Finset (ZMod p)}
-- given
  (hA : ∀ a ∈ A, (a : ZMod p) ≠ 0) :
-- imply
  ∑ t : ZMod p, (A.filter (fun a : ℤ => t * (a : ZMod p) ∈ B)).card = A.card * B.card := by
-- proof
  have step1 : ∀ t : ZMod p, (A.filter (fun a : ℤ => t * (a : ZMod p) ∈ B)).card =
    ∑ a ∈ A, if t * (a : ZMod p) ∈ B then 1 else 0 := fun t => Finset.card_filter _ A
  simp_rw [step1, Finset.sum_comm (s := Finset.univ) (t := A)]
  have step2 : ∀ a ∈ A, ∑ t : ZMod p, (if t * (a : ZMod p) ∈ B then 1 else 0 : ℕ) = B.card := by
    intro a ha
    have h := card_filter_mul_right (hA a ha) B
    rw [Finset.card_filter] at h; exact h
  rw [Finset.sum_congr rfl step2, Finset.sum_const, smul_eq_mul]

end SumFree

namespace SumFree

/--
[intCast_ne_zero_of_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/SumFree.lean)
-/
@[path]
lemma intCast_ne_zero_of_lt
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {a : ℤ}
-- given
  (ha : a ≠ 0)
  (hap : a.natAbs < p) :
-- imply
  (a : ZMod p) ≠ 0 := by
-- proof
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  intro hdvd
  have h1 : (p : ℤ) ≤ |a| := Int.le_of_dvd (abs_pos.mpr ha) ((dvd_abs _ _).mpr hdvd)
  rw [Int.abs_eq_natAbs] at h1
  exact absurd (show (a.natAbs : ℤ) < (p : ℤ) from by exact_mod_cast hap) (not_lt.mpr h1)

end SumFree

namespace SumFree

/--
[erdos_sumFree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/SumFree.lean)
-/
@[path]
lemma erdos_sumFree
  {A : Finset ℤ}
-- given
  (hA : ∀ a ∈ A, a ≠ 0) :
-- imply
  ∃ S ⊆ A, IsSumFree S ∧ A.card / 3 ≤ S.card := by
-- proof
  classical
  obtain hAe | hAne := A.eq_empty_or_nonempty
  · exact ⟨∅, empty_subset _, fun _ h => absurd h (Finset.notMem_empty _), by subst hAe; simp⟩
  set M := A.sup' hAne (fun a => a.natAbs)
  have hprime_exists : ∃ p : ℕ, Nat.Prime p ∧ p % 3 = 2 ∧ M < p ∧ 4 < p := by
    have hinf := Nat.infinite_setOf_prime_and_eq_mod (a := (2 : ZMod 3)) (by decide)
    obtain ⟨p, hp, hN⟩ := hinf.exists_gt (max M 4)
    exact ⟨p, hp.1, (congr_arg ZMod.val hp.2).trans rfl, by omega, by omega⟩
  obtain ⟨p, hpp, hp3, hpM, hp4⟩ := hprime_exists
  haveI : Fact (Nat.Prime p) := ⟨hpp⟩
  have hp2 : 2 < p := by omega
  have hAmod : ∀ a ∈ A, (a : ZMod p) ≠ 0 := fun a ha =>
    intCast_ne_zero_of_lt (hA a ha) (Nat.lt_of_le_of_lt (Finset.le_sup' _ ha) hpM)
  set B := Finset.univ.filter (fun x : ZMod p => p / 3 < ZMod.val x ∧ ZMod.val x ≤ 2 * p / 3)
  have hBcard : B.card = 2 * p / 3 - p / 3 := card_filter_val_Ioc p (p / 3) (2 * p / 3) (by omega)
  have h0B : (0 : ZMod p) ∉ B := by
    simp only [B, mem_filter, mem_univ, true_and, ZMod.val_zero]
    omega
  have hf0 : (A.filter (fun a : ℤ => (0 : ZMod p) * (a : ZMod p) ∈ B)).card = 0 := by
    convert Finset.card_empty (α := ℤ)
    rw [Finset.eq_empty_iff_forall_notMem]
    intro a
    simp only [mem_filter, zero_mul, not_and_or]
    exact Or.inr h0B
  have hsum : ∑ t : ZMod p, (A.filter (fun a : ℤ => t * (a : ZMod p) ∈ B)).card =
    A.card * B.card := double_count A B hAmod
  set f : ZMod p → ℕ := fun t => (A.filter (fun a : ℤ => t * (a : ZMod p) ∈ B)).card
  have hnonzero_sum : ∑ t ∈ (Finset.univ : Finset (ZMod p)).filter (· ≠ 0), f t =
    A.card * B.card := by
    have hfsum : ∑ t : ZMod p, f t = A.card * B.card := hsum
    have hsplit := Finset.sum_filter_add_sum_filter_not
      (Finset.univ : Finset (ZMod p)) (· ≠ (0 : ZMod p)) f
    have hzero_part : ∑ x ∈ Finset.univ.filter (fun x => ¬(x ≠ (0 : ZMod p))), f x = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      simp only [mem_filter, mem_univ, true_and, not_not] at ht
      rwa [show f t = f 0 from by rw [ht]]
    linarith
  have hcard_nz : (Finset.univ.filter (· ≠ (0 : ZMod p))).card = p - 1 := by
    rw [Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
      Finset.card_univ, ZMod.card p]
  have harith : (p - 1) * (A.card / 3) ≤ A.card * B.card := by
    rw [hBcard]
    obtain ⟨m, hm⟩ : ∃ m, p = 3 * m + 2 := ⟨p / 3, by omega⟩
    subst hm
    simp only [show (3 * m + 2) / 3 = m from by omega,
      show 2 * (3 * m + 2) / 3 = 2 * m + 1 from by omega,
      show 3 * m + 2 - 1 = 3 * m + 1 from by omega,
      show 2 * m + 1 - m = m + 1 from by omega]
    nlinarith [Nat.div_mul_le_self A.card 3]
  have havg : ∃ t ∈ (Finset.univ : Finset (ZMod p)).filter (· ≠ 0),
    A.card / 3 ≤ f t := by
    by_contra H
    push Not at H
    have hlt : ∑ t ∈ Finset.univ.filter (· ≠ (0 : ZMod p)), f t <
      (Finset.univ.filter (· ≠ (0 : ZMod p))).card * (A.card / 3) :=
      calc ∑ t ∈ Finset.univ.filter (· ≠ (0 : ZMod p)), f t
        < ∑ _t ∈ Finset.univ.filter (· ≠ (0 : ZMod p)), A.card / 3 :=
          Finset.sum_lt_sum_of_nonempty ⟨1, by simp [mem_filter, one_ne_zero]⟩ H
        _ = _ := by rw [Finset.sum_const, smul_eq_mul]
    rw [hcard_nz] at hlt
    linarith
  obtain ⟨t, ht_mem, ht_card⟩ := havg
  have ht_ne : t ≠ 0 := (Finset.mem_filter.mp ht_mem).2
  refine ⟨A.filter (fun a : ℤ => t * (a : ZMod p) ∈ B), Finset.filter_subset _ _, ?_, ht_card⟩
  intro a ha b hb c hc habc
  simp only [mem_filter] at ha hb hc
  have htc_eq : t * (c : ZMod p) = t * (a : ZMod p) + t * (b : ZMod p) := by
    rw [← habc]; push_cast; ring
  rw [htc_eq] at hc
  simp only [B, mem_filter, mem_univ, true_and] at ha hb hc
  exact middleThird_sumFree hp3 hp2 ha.2.1 ha.2.2 hb.2.1 hb.2.2 hc.2

end SumFree


-- created on 2026-10-23
