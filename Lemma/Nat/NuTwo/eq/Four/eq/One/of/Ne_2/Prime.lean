import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_GenusNumerics
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_nuTwo_prime](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_nuTwo_prime.lean)
-/
@[path]
private lemma main
  {p : ℕ}
-- given
  (hp : p.Prime)
  (hp2 : p ≠ 2) :
-- imply
  nuTwo p = if p % 4 = 1 then 2 else 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsq_iff : ∀ {s x : ZMod p}, s ^ 2 + 1 = 0 → (x ^ 2 + 1 = 0 ↔ x = s ∨ x = -s) := by
-- proof
    intro s x hs
    constructor
    ·
      intro hx
      have hfac : (x - s) * (x + s) = 0 := by linear_combination hx - hs
      rcases mul_eq_zero.mp hfac with hd | hd
      · exact Or.inl (by linear_combination hd)
      · exact Or.inr (by linear_combination hd)
    ·
      rintro (rfl | rfl)
      · exact hs
      · linear_combination hs
  have hne_neg : ∀ {s : ZMod p}, s ^ 2 + 1 = 0 → s ≠ -s := by
    intro s hs hcontra
    have h2s : (2 : ZMod p) * s = 0 := by linear_combination hcontra
    rcases mul_eq_zero.mp h2s with h2 | hs0
    ·
      have hcast : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h2
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp hcast
      refine hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    ·
      have hs_ne : s ≠ 0 := by
        rintro rfl
        exact one_ne_zero (α := ZMod p) (by linear_combination hs)
      refine hs_ne hs0
  by_cases h1 : p % 4 = 1
  ·
    rw [ite_eq_left h1]
    obtain ⟨s, hs⟩ : IsSquare (-1 : ZMod p) :=
      ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
    have hs2 : s ^ 2 + 1 = 0 := by linear_combination -hs
    have hns2 : (-s) ^ 2 + 1 = 0 := by linear_combination hs2
    show Nat.card {x : ZMod p // x ^ 2 + 1 = 0} = 2
    rw [Nat.card_eq_two_iff]
    refine ⟨⟨s, hs2⟩, ⟨-s, hns2⟩, ?_, ?_⟩
    ·
      simp only [ne_eq, Subtype.mk.injEq]
      exact hne_neg hs2
    ·
      rw [Set.eq_univ_iff_forall]
      rintro ⟨x, hx⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.mk.injEq]
      exact (hsq_iff hs2).mp hx
  ·
    rw [ite_eq_right h1]
    have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
    have hns : ¬IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]
      omega
    have hempty : IsEmpty {x : ZMod p // x ^ 2 + 1 = 0} := by
      refine ⟨fun z => ?_⟩
      obtain ⟨x, hx⟩ := z
      exact hns ⟨x, by linear_combination -hx⟩
    refine @Nat.card_of_isEmpty _ hempty


-- created on 2026-10-23
