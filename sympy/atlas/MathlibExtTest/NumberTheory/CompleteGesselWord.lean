/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/CompleteGesselWord.lean -/


import sympy.atlas.NumberTheory.CompleteGesselWord
import Lemma.Nat.CompleteGesselWord

namespace MetaMathlibExt

/-- The empty word over the empty alphabet is complete. -/
example : IsCompleteGesselWord 0 [] := by
  refine ⟨?_, ?_⟩
  · intro w' suffix _ k _ hkn
    omega
  · intro i
    nomatch i

/-- The balanced one-letter word `1, bar 1` is complete. -/
example : IsCompleteGesselWord 1 [Sum.inl (0 : Fin 1), Sum.inr (0 : Fin 1)] := by
  refine ⟨?_, ?_⟩
  · intro w' suffix h k hk1 hkn
    have hk : k = 1 := by omega
    subst hk
    rw [Finset.Icc_self, Finset.sum_singleton]
    have hp := eq_nil_or_eq_singleton_or_eq_pair_of_append_eq_pair
      (Sum.inl (0 : Fin 1)) (Sum.inr (0 : Fin 1)) w' suffix h
    rcases hp with rfl | rfl | rfl <;> decide
  · decide

/-- The unbalanced one-letter word `1` is not complete. -/
example : ¬ IsCompleteGesselWord 1 [Sum.inl (0 : Fin 1)] := by
  intro h
  obtain ⟨_, hcount⟩ := h
  exact absurd (hcount ⟨0, by decide⟩) (by decide)

end MetaMathlibExt
