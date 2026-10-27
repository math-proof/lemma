import Mathlib
import Initialize.Tactic.Attr.Basic
open IntermediateField Module Polynomial


namespace IsPurelyInseparable

/--
[exists_minpoly_X_pow_sub_C_of_finrank_eq_prime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/PurelyInseparablePrimeDegree.lean)
-/
@[path]
lemma exists_minpoly_X_pow_sub_C_of_finrank_eq_prime
  [Field K] [Field L] [Algebra K L] [IsPurelyInseparable K L] [FiniteDimensional K L]
  {p : ℕ} [CharP K p]
-- given
  (hp : p.Prime)
  (hfin : finrank K L = p) :
-- imply
  ∃ α : L, ∃ a : K,
      minpoly K α = X ^ p - C a ∧
        (∀ b : K, b ^ p ≠ a) ∧ K⟮α⟯ = ⊤ := by
-- proof
  have _ := Fact.mk hp
  have hbot_ne_top : (⊥ : IntermediateField K L) ≠ ⊤ := by
    intro hcon
    have h1 : finrank K (↥(⊥ : IntermediateField K L)) = 1 :=
      IntermediateField.finrank_bot
    have h2 : finrank K (↥(⊤ : IntermediateField K L)) = finrank K L :=
      IntermediateField.finrank_top'
    have hp1 : p ≠ 1 := hp.ne_one
    rw [hcon] at h1
    omega
  have hlt : (⊥ : IntermediateField K L) < ⊤ := lt_of_le_of_ne bot_le hbot_ne_top
  obtain ⟨α, _, hα⟩ := SetLike.exists_of_lt hlt
  have hint : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hdeg_adjoin : finrank K K⟮α⟯ = (minpoly K α).natDegree :=
    IntermediateField.adjoin.finrank hint
  have htower : finrank K K⟮α⟯ * finrank K⟮α⟯ L = finrank K L :=
    Module.finrank_mul_finrank K K⟮α⟯ L
  have hdvd : finrank K K⟮α⟯ ∣ p := ⟨_, (htower.trans hfin).symm⟩
  have hne_one : finrank K K⟮α⟯ ≠ 1 :=
    mt IntermediateField.finrank_adjoin_simple_eq_one_iff.mp hα
  have hfin_adjoin : finrank K K⟮α⟯ = p := by
    obtain h | h := (Nat.dvd_prime hp).mp hdvd
    · exact absurd h hne_one
    · exact h
  have hdeg : (minpoly K α).natDegree = p := by omega
  obtain ⟨n, a, hmin⟩ := IsPurelyInseparable.minpoly_eq_X_pow_sub_C (F := K) (E := L)
    (q := p) (x := α)
  have hpn : p ^ n = p := by
    have hcon := hdeg
    rwa [hmin, Polynomial.natDegree_X_pow_sub_C] at hcon
  have hn1 : n = 1 := Nat.pow_right_injective hp.one_lt (by simpa using hpn)
  subst hn1
  rw [pow_one] at hmin
  refine ⟨α, a, hmin, ?_, ?_⟩
  · intro b hb
    have hirr : Irreducible (X ^ p - C a : K[X]) :=
      hmin ▸ minpoly.irreducible hint
    have hsub : ((X - C b : K[X]) ^ p) = X ^ p - C (b ^ p) := by
      rw [sub_pow_expChar, map_pow]
    rw [hb] at hsub
    rw [← hsub] at hirr
    exact not_irreducible_pow hp.ne_one hirr
  · rw [Field.primitive_element_iff_minpoly_natDegree_eq (F := K) (E := L)
    (α := α), hmin,
    Polynomial.natDegree_X_pow_sub_C, hfin]

end IsPurelyInseparable


-- created on 2026-10-20
-- updated on 2026-10-26
