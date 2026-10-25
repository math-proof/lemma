import Mathlib
import sympy.Basic
import Lemma.ModularCurve.GenusNumerics
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_nuThree_prime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_nuThree_prime.lean)
-/
@[path]
private lemma main
  {p : ℕ}
-- given
  (hp : p.Prime)
  (hp3 : p ≠ 3) :
-- imply
  nuThree p = if p % 3 = 1 then 2 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord_iff : ∀ x : ZMod p, x ^ 2 + x + 1 = 0 ↔ orderOf x = 3 := by
-- proof
    intro x
    constructor
    ·
      intro hx
      refine orderOf_eq_prime ?_ ?_
      · linear_combination (x - 1) * hx
      ·
        rintro rfl
        have h3 : (3 : ZMod p) = 0 := by linear_combination hx
        have hcast : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
          ((CharP.cast_eq_zero_iff (ZMod p) p 3).mp hcast))
    ·
      intro hx
      have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
      have hx1 : x ≠ 1 := by rintro rfl; rw [orderOf_one] at hx; omega
      have hfac : (x - 1) * (x ^ 2 + x + 1) = 0 := by linear_combination hx3
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd (by linear_combination h : x = 1) hx1
      · exact h
  by_cases h1 : p % 3 = 1
  ·
    rw [ite_eq_left h1]
    have hdvd : 3 ∣ Fintype.card (ZMod p)ˣ := by
      rw [ZMod.card_units p]; have := hp.two_le; omega
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card 3 hdvd
    have hζord : orderOf (u : ZMod p) = 3 := by rw [orderOf_units]; exact hu
    have hζ : (u : ZMod p) ^ 2 + (u : ZMod p) + 1 = 0 := (hord_iff _).mpr hζord
    set ζ := (u : ZMod p) with hζdef
    have hζ' : (-1 - ζ) ^ 2 + (-1 - ζ) + 1 = 0 := by linear_combination hζ
    have hne : ζ ≠ -1 - ζ := by
      intro hcontra
      have h3 : (3 : ZMod p) = 0 := by linear_combination 4 * hζ - (2 * ζ + 1) * hcontra
      have hcast : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h3
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp
        ((CharP.cast_eq_zero_iff (ZMod p) p 3).mp hcast))
    show Nat.card {x : ZMod p // x ^ 2 + x + 1 = 0} = 2
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨ζ, hζ⟩, ⟨-1 - ζ, hζ'⟩, ?_, ?_⟩
    ·
      simp only [ne_eq, Subtype.mk.injEq]
      exact hne
    ·
      rw [Set.eq_univ_iff_forall]
      rintro ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.mk.injEq]
      have hfac : (x - ζ) * (x + ζ + 1) = 0 := by linear_combination hx - hζ
      rcases mul_eq_zero.mp hfac with hd | hd
      · exact Or.inl (by linear_combination hd)
      · exact Or.inr (by linear_combination hd)
  ·
    rw [ite_eq_right h1]
    have hempty : IsEmpty {x : ZMod p // x ^ 2 + x + 1 = 0} := by
      refine ⟨fun z => ?_⟩
      obtain ⟨x, hx⟩ := z
      have hord : orderOf x = 3 := (hord_iff x).mp hx
      have hx0 : x ≠ 0 := by
        rintro rfl; exact one_ne_zero (α := ZMod p) (by linear_combination hx)
      have hdvd : (3 : ℕ) ∣ p - 1 := by
        rw [← hord]; exact ZMod.orderOf_dvd_card_sub_one hx0
      have := hp.two_le; omega
    refine @Nat.card_of_isEmpty _ hempty


-- created on 2026-10-23
