/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/Arrow.lean -/

import Mathlib.Data.Fintype.Basic
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.SuccPred
import Def.GameTheory.SocialChoice.Arrow.Part2


section

namespace MathlibExt.GameTheory.SocialChoice.ArrowWanted

lemma rank3_injective {Alt : Type*} [Fintype Alt] [DecidableEq Alt]
    (x y z : Alt) (h1 : x ≠ y) (h2 : x ≠ z) (h3 : y ≠ z) :
    Function.Injective (rank3 (Alt := Alt) x y z) := by
  intro a b h
  have e1 : a = x ∨ a = y ∨ a = z ∨ (a ≠ x ∧ a ≠ y ∧ a ≠ z) := by
    by_cases ha1 : a = x
    · exact Or.inl ha1
    · by_cases ha2 : a = y
      · exact Or.inr (Or.inl ha2)
      · by_cases ha3 : a = z
        · exact Or.inr (Or.inr (Or.inl ha3))
        · exact Or.inr (Or.inr (Or.inr ⟨ha1, ha2, ha3⟩))
  have e2 : b = x ∨ b = y ∨ b = z ∨ (b ≠ x ∧ b ≠ y ∧ b ≠ z) := by
    by_cases hb1 : b = x
    · exact Or.inl hb1
    · by_cases hb2 : b = y
      · exact Or.inr (Or.inl hb2)
      · by_cases hb3 : b = z
        · exact Or.inr (Or.inr (Or.inl hb3))
        · exact Or.inr (Or.inr (Or.inr ⟨hb1, hb2, hb3⟩))
  unfold rank3 at h
  rcases e1 with rfl | rfl | rfl | ⟨ha1, ha2, ha3⟩ <;>
    rcases e2 with rfl | rfl | rfl | ⟨hb1, hb2, hb3⟩ <;>
    simp_all [Ne.symm h1, Ne.symm h2, Ne.symm h3]
  all_goals try omega
  exact baseRank_injective (by omega)

end MathlibExt.GameTheory.SocialChoice.ArrowWanted
end
