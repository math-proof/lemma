/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/IdentityProductNecklace.lean -/

import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Torsor.Defs
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Def.Combinatorics.Enumerative.IdentityProductNecklace.Part5


section

namespace MetaMathlibExt

/-- The number of identity-product necklaces over a finite group equals Burnside's average over
rotations. Source: Darij Grinberg and Peter Mao, "Necklaces over a Group with Identity Product,"
Journal of Integer Sequences 29 (2026), Article 26.4.6, Theorem 1 (`thm.main`), lines 186–195,
<https://cs.uwaterloo.ca/journals/JIS/VOL29/Grinberg/grinberg2.tex>. Identity-product tuples,
divisor-count notation, and necklaces defined at lines 140–180.

Proves `Wanted` entry `identity_product_necklace_count`.
-/
theorem identity_product_necklace_count (G : Type*) [Group G] [Fintype G]
  [DecidableEq G] (n : ℕ) (hn : 0 < n) :
  (Set.ncard
  { O : Set (Fin n → G) | ∃ x : Fin n → G, (List.ofFn x).prod = 1 ∧ O =
  { y | ∃ m : ℕ, m < n ∧ ∀ i : Fin n, y i = x ⟨(i.val + m) % n, Nat.mod_lt _ hn⟩ } } : ℚ) =
  (1 / (n : ℚ)) * Finset.sum (Nat.divisors n)
  (fun d => (Nat.totient (n / d) : ℚ) * (Fintype.card { g : G // g ^ (n / d) = 1 } : ℚ) *
  ((Fintype.card G : ℚ) ^ (d - 1))) := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  have hSeq : {O : Set (Fin n → G) | ∃ x : Fin n → G, (List.ofFn x).prod = 1 ∧
        O = {y | ∃ m : ℕ, m < n ∧ ∀ i : Fin n,
          y i = x ⟨(i.val + m) % n, Nat.mod_lt _ hn⟩}}
      = {O : Set (Fin n → G) | ∃ x : Fin n → G, (List.ofFn x).prod = 1 ∧
        O = orbSet G n x} := rfl
  rw [hSeq]
  have hSr := neck_range G n _ rfl
  rw [hSr, Set.ncard_image_of_injective _ (neckQuot_injective G n),
    Set.ncard_univ, Nat.card_eq_fintype_card]
  have hBurn := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup
    (ZMod n) {x : Fin n → G // (List.ofFn x).prod = 1}
  rw [ZMod.card n] at hBurn
  have hmaps : ∀ k ∈ (Finset.univ : Finset (ZMod n)),
      addOrderOf k ∈ Nat.divisors n := by
    intro k _
    have hcd : addOrderOf k ∣ Fintype.card (ZMod n) := addOrderOf_dvd_card
    rw [ZMod.card n] at hcd
    exact Nat.mem_divisors.mpr ⟨hcd, hn.ne'⟩
  have hfib : ∀ e ∈ Nat.divisors n,
      (Finset.univ.filter (fun k : ZMod n => addOrderOf k = e)).card
        = e.totient := by
    intro e he
    have hdd : e ∣ n := (Nat.mem_divisors.mp he).1
    have hdiv : e ∣ Fintype.card (ZMod n) := by rwa [ZMod.card n]
    exact IsAddCyclic.card_addOrderOf_eq_totient hdiv
  have hgroup : (Finset.sum Finset.univ (fun k : ZMod n => Fintype.card
        ↥(AddAction.fixedBy {x : Fin n → G // (List.ofFn x).prod = 1} k)))
      = Finset.sum (Nat.divisors n) (fun e => (e.totient
        * Fintype.card {g : G // g ^ e = 1} * (Fintype.card G) ^ (n / e - 1))) := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun k => Fintype.card ↥(AddAction.fixedBy
        {x : Fin n → G // (List.ofFn x).prod = 1} k))]
    refine Finset.sum_congr rfl (fun e he => ?_)
    have hinner : ∀ k ∈ Finset.univ.filter (fun k : ZMod n => addOrderOf k = e),
        Fintype.card ↥(AddAction.fixedBy
          {x : Fin n → G // (List.ofFn x).prod = 1} k)
        = (Fintype.card G) ^ (n / e - 1)
          * Fintype.card {g : G // g ^ e = 1} := by
      intro k hk
      have hke : addOrderOf k = e := (Finset.mem_filter.mp hk).2
      rw [card_fixedBy G n k, hke]
    rw [Finset.sum_congr rfl (fun k hk => hinner k hk), Finset.sum_const,
      hfib e he]
    simp only [nsmul_eq_mul, Nat.cast_id]
    ring
  have hreindex : (Finset.sum (Nat.divisors n) (fun e => (e.totient
        * Fintype.card {g : G // g ^ e = 1} * (Fintype.card G) ^ (n / e - 1))))
      = Finset.sum (Nat.divisors n) (fun d => ((Nat.totient (n / d))
        * Fintype.card {g : G // g ^ (n / d) = 1} * (Fintype.card G) ^ (d - 1))) := by
    refine Finset.sum_bij (fun e _ => n / e) ?maps ?inj ?surj ?val
    · intro e he
      exact Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp he).1, hn.ne'⟩
    · intro a ha b hb hab
      have ha' : a ∣ n := (Nat.mem_divisors.mp ha).1
      have hb' : b ∣ n := (Nat.mem_divisors.mp hb).1
      have e1 : n / (n / a) = a := Nat.div_div_self ha' hn.ne'
      have e2 : n / (n / b) = b := Nat.div_div_self hb' hn.ne'
      rw [hab] at e1
      exact e1.symm.trans e2
    · intro d hd
      have hd' : d ∣ n := (Nat.mem_divisors.mp hd).1
      refine ⟨n / d, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd', hn.ne'⟩, ?_⟩
      exact Nat.div_div_self hd' hn.ne'
    · intro e he
      rw [Nat.div_div_self (Nat.mem_divisors.mp he).1 hn.ne']
  have hQcard : Fintype.card (Quotient (AddAction.orbitRel (ZMod n)
        {x : Fin n → G // (List.ofFn x).prod = 1})) * n
      = Finset.sum (Nat.divisors n) (fun d => ((Nat.totient (n / d))
        * Fintype.card {g : G // g ^ (n / d) = 1} * (Fintype.card G) ^ (d - 1))) := by
    rw [← hBurn, hgroup, hreindex]
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hc : ((Fintype.card (Quotient (AddAction.orbitRel (ZMod n)
        {x : Fin n → G // (List.ofFn x).prod = 1})) : ℚ) * (n : ℚ))
      = Finset.sum (Nat.divisors n) (fun d => ((Nat.totient (n / d) : ℚ)
        * (Fintype.card {g : G // g ^ (n / d) = 1} : ℚ)
        * ((Fintype.card G : ℚ) ^ (d - 1)))) := by
    have h := congrArg (Nat.cast (R := ℚ)) hQcard
    simpa [Nat.cast_mul, Nat.cast_pow, Nat.cast_sum] using h
  calc ((Fintype.card (Quotient (AddAction.orbitRel (ZMod n)
        {x : Fin n → G // (List.ofFn x).prod = 1})) : ℚ))
      = (((Fintype.card (Quotient (AddAction.orbitRel (ZMod n)
        {x : Fin n → G // (List.ofFn x).prod = 1})) : ℚ) * (n : ℚ)) / (n : ℚ)) := by
        field_simp
    _ = _ := by rw [hc]; ring

end MetaMathlibExt
end
