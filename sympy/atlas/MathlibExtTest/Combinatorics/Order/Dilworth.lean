/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Order/Dilworth.lean -/


import sympy.atlas.Combinatorics.Order.Dilworth
import Lemma.Finset.Order.Dilworth
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Order.Defs.PartialOrder


namespace MathlibExt.Combinatorics.Order.DilworthWanted

-- Empty order: the empty family is a chain cover.
example : maxAntichainSize Empty = 0 := by
  obtain ⟨A, -, hA⟩ := exists_isAntichain_card_eq_maxAntichainSize (α := Empty)
  rw [← hA, Finset.eq_empty_of_isEmpty A, Finset.card_empty]

example : minChainCoverSize Empty = 0 :=
  Nat.le_zero.mp (minChainCoverSize_le_card (C := ∅) ⟨by simp, fun a => a.elim⟩)

-- Total order: `univ` is a chain, so every antichain is a singleton.
example : maxAntichainSize (Fin 3) = 1 := by
  refine le_antisymm ?_ (card_le_maxAntichainSize (A := {0}) (by simp))
  rw [dilworth_decomposition]
  refine minChainCoverSize_le_card (C := {Finset.univ}) ⟨?_, fun a => ?_⟩
  · simpa using isChain_of_trichotomous _
  · exact ⟨_, Finset.mem_singleton_self _, Finset.mem_univ a⟩

example : ∃ A : Finset (Fin 3), IsAntichain (· ≤ ·) (A : Set (Fin 3)) ∧ A.card ≤ 1 := by
  obtain ⟨A, hA, -⟩ := exists_isAntichain_card_eq_maxAntichainSize (α := Fin 3)
  exact ⟨A, hA, Finset.card_le_one.mpr fun a ha b hb => hA.subsingleton ha hb⟩

/-- `Fin 3` with the discrete order: distinct elements are incomparable. -/
def Discrete3 := Fin 3

instance : Fintype Discrete3 := inferInstanceAs (Fintype (Fin 3))
instance : DecidableEq Discrete3 := inferInstanceAs (DecidableEq (Fin 3))
instance : PartialOrder Discrete3 where
  le := Eq
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

-- Discrete order: `univ` is an antichain, so every chain cover needs one chain per element.
example : minChainCoverSize Discrete3 = 3 := by
  rw [← dilworth_decomposition]
  obtain ⟨A, -, hA⟩ := exists_isAntichain_card_eq_maxAntichainSize (α := Discrete3)
  refine le_antisymm (hA ▸ Finset.card_le_univ A) ?_
  exact card_le_maxAntichainSize (A := Finset.univ) fun _ _ _ _ hab h => hab (discrete3_le.mp h)

example : ∃ C : Finset (Finset Discrete3), IsChainCoverFin C ∧ 3 ≤ C.card := by
  obtain ⟨C, hC, hcard⟩ := exists_isChainCoverFin_card_eq_minChainCoverSize (α := Discrete3)
  refine ⟨C, hC, hcard ▸ ?_⟩
  rw [← dilworth_decomposition]
  exact card_le_maxAntichainSize (A := Finset.univ) fun _ _ _ _ hab h => hab (discrete3_le.mp h)

end MathlibExt.Combinatorics.Order.DilworthWanted
