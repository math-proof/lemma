import Mathlib
import sympy.Basic

open IntermediateField
open Polynomial

/--
[IntermediateField_finrank_adjoin_rootsOfUnity_eq_card_rootSet](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_finrank_adjoin_rootsOfUnity_eq_card_rootSet.lean)
-/
@[main]
private lemma main
  {F E : Type} [Field F] [Field E] [Algebra F E] [IsAlgClosed E] [CharZero F]
  {m : ℕ}
  {ζ₀ : E}
-- given
  (hm : 0 < m)
  (hζ₀ : IsPrimitiveRoot ζ₀ m) :
-- imply
  Module.finrank F (IntermediateField.adjoin F {ζ : E | ζ ^ m = 1})
      = Fintype.card ((minpoly F ζ₀).rootSet E) := by
-- proof
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  have hint : IsIntegral F ζ₀ := IsIntegral.of_pow hm (by rw [hζ₀.pow_eq_one]; exact isIntegral_one)
  have h1 : IntermediateField.adjoin F {ζ : E | ζ ^ m = 1} = F⟮ζ₀⟯ := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro ζ hζ
      obtain ⟨i, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
      exact pow_mem (IntermediateField.mem_adjoin_simple_self F ζ₀) i
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact IntermediateField.subset_adjoin F _ hζ₀.pow_eq_one
  rw [LinearEquiv.finrank_eq (IntermediateField.equivOfEq h1).toLinearEquiv, IntermediateField.adjoin.finrank hint,
    Polynomial.card_rootSet_eq_natDegree (minpoly.irreducible hint).separable (IsAlgClosed.splits _)]


-- created on 2026-10-05
