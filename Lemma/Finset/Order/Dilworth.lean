import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Order.Dilworth
open MathlibExt.Combinatorics.Order.DilworthWanted


/--
[card_le_maxAntichainSize](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/Dilworth.lean)
-/
@[path]
private lemma card_le_maxAntichainSize_eq
  [Fintype α] [PartialOrder α]
  {A : Finset α}
-- given
  (hA : IsAntichain (· ≤ ·) (A : Set α)) :
-- imply
  A.card ≤ maxAntichainSize α := by
-- proof
  apply MathlibExt.Combinatorics.Order.DilworthWanted.card_le_maxAntichainSize hA

/--
[minChainCoverSize_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/Dilworth.lean)
-/
@[path]
private lemma minChainCoverSize_le_card_eq
  :
-- imply
  {α : Type*} [Fintype α] [PartialOrder α]
    {C : Finset (Finset α)} (hC : IsChainCoverFin (α := by
-- proof
  apply MathlibExt.Combinatorics.Order.DilworthWanted.minChainCoverSize_le_card

/--
[dilworth_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/Dilworth.lean)
-/
@[path]
private lemma dilworth_decomposition_eq
  [Fintype α] [PartialOrder α] :
-- imply
  maxAntichainSize α = minChainCoverSize α := by
-- proof
  apply MathlibExt.Combinatorics.Order.DilworthWanted.dilworth_decomposition

/--
[exists_isAntichain_card_eq_maxAntichainSize](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/Dilworth.lean)
-/
@[path]
private lemma exists_isAntichain_card_eq_maxAntichainSize_eq
  [Fintype α] [PartialOrder α] :
-- imply
  ∃ A : Finset α, IsAntichain (· ≤ ·) (A : Set α) ∧ A.card = maxAntichainSize α := by
-- proof
  apply MathlibExt.Combinatorics.Order.DilworthWanted.exists_isAntichain_card_eq_maxAntichainSize

/--
[exists_isChainCoverFin_card_eq_minChainCoverSize](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/Dilworth.lean)
-/
@[path]
private lemma exists_isChainCoverFin_card_eq_minChainCoverSize_eq
  [Fintype α] [PartialOrder α] :
-- imply
  ∃ C : Finset (Finset α), IsChainCoverFin C ∧ C.card = minChainCoverSize α := by
-- proof
  apply MathlibExt.Combinatorics.Order.DilworthWanted.exists_isChainCoverFin_card_eq_minChainCoverSize


-- created on 2026-10-20
