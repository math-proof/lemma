import Mathlib
import sympy.Basic

open scoped Classical
open CategoryTheory CategoryTheory.MonoidalCategory Module

/--
[Representation_trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Representation_trace_mul_eq_trace_of_commute_of_pow_prime_pow_eq_one.lean)
-/
@[main]
private lemma main
  [Field k] [Group G] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  {p : ℕ} [Fact p.Prime] [CharP k p]
  {ρ : Representation k G V}
  {g u : G}
  {a : ℕ}
-- given
  (hgu : Commute g u)
  (hu : u ^ p ^ a = 1) :
-- imply
  LinearMap.trace k V (ρ (g * u)) = LinearMap.trace k V (ρ g) := by
-- proof
  rcases subsingleton_or_nontrivial V with hV | hV
  ·
    have h : ρ (g * u) = ρ g := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [h]
  · haveI : CharP (Module.End k V) p :=
      charP_of_injective_algebraMap (algebraMap k (Module.End k V)).injective p

    set N : Module.End k V := ρ u - 1 with hN
    have hNp : N ^ p ^ a = 0 := by
      rw [hN, sub_pow_char_pow_of_commute p a (Commute.one_right _), one_pow, ← map_pow, hu,
        map_one, sub_self]
    have hNil : IsNilpotent N := ⟨p ^ a, hNp⟩

    have hcomm : Commute (ρ g) N := (hgu.map ρ).sub_right (Commute.one_right _)
    have hgN : IsNilpotent (ρ g * N) := hcomm.isNilpotent_mul_left hNil
    have htr : LinearMap.trace k V (ρ g * N) = 0 :=
      (LinearMap.isNilpotent_trace_of_isNilpotent hgN).eq_zero
    have hsplit : ρ (g * u) = ρ g + ρ g * N := by
      rw [map_mul, hN, mul_sub, mul_one, add_sub_cancel]
    rw [hsplit, map_add, htr, add_zero]


-- created on 2026-10-05
