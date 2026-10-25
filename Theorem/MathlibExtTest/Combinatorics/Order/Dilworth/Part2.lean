/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Order/Dilworth.lean -/


import Def.Combinatorics.Order.Dilworth
import Lemma.Finset.Order.Dilworth
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Order.Defs.PartialOrder
import Instance.MathlibExtTest.Combinatorics.Order.Dilworth


namespace MathlibExt.Combinatorics.Order.DilworthWanted

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
