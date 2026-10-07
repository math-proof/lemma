import Mathlib
import sympy.Basic


/--
[Submodule_eq_span_singleton_of_card_eq_sq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_eq_span_singleton_of_card_eq_sq.lean)
-/
@[main]
private lemma main
  [AddCommGroup V]
  {p : ℕ} [Fact p.Prime] [Module (ZMod p) V]
  {N : Submodule (ZMod p) V}
  {v : V}
-- given
  (hV : Nat.card V = p ^ 2)
  (htop : N ≠ ⊤)
  (hv : v ∈ N)
  (hv0 : v ≠ 0) :
-- imply
  N = Submodule.span (ZMod p) {v} := by
-- proof
  have hp : p.Prime := Fact.out
  have : Finite V := Nat.finite_of_card_ne_zero (by rw [hV]; exact pow_ne_zero _ hp.ne_zero)
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite

  have h2 : Module.finrank (ZMod p) V = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    rw [hV, Nat.card_zmod] at h
    exact (Nat.pow_right_injective hp.two_le h).symm

  have hlt : Module.finrank (ZMod p) N < 2 := h2 ▸ Submodule.finrank_lt htop
  have hbot : N ≠ ⊥ := fun h => hv0 ((Submodule.mem_bot (R := ZMod p)).mp (h ▸ hv))
  have hpos : 0 < Module.finrank (ZMod p) N := by
    rw [Module.finrank_pos_iff_exists_ne_zero]
    exact ⟨⟨v, hv⟩, fun h => hv0 (congrArg Subtype.val h)⟩
  have hN1 : Module.finrank (ZMod p) N = 1 := by omega

  symm
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hv
  · rw [finrank_span_singleton hv0, hN1]


-- created on 2026-10-05
