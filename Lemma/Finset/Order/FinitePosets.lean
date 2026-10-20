import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Order.FinitePosets
open MathlibExt.Combinatorics.Order.FinitePosets


/--
[isAntichainCoverFin_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/FinitePosets.lean)
-/
@[path]
private lemma isAntichainCoverFin_iff_eq
  [PartialOrder α]
  {C : Finset (Finset α)} :
-- imply
  IsAntichainCoverFin C ↔ (∀ s ∈ C, IsAntichain (· ≤ ·) (s : Set α)) ∧ ∀ a : α, ∃ s ∈ C, a ∈ s := by
-- proof
  apply MathlibExt.Combinatorics.Order.FinitePosets.isAntichainCoverFin_iff C

/--
[card_le_maxChainSize](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/FinitePosets.lean)
-/
@[path]
private lemma card_le_maxChainSize_eq
  [Fintype α] [PartialOrder α]
  {s : Finset α}
-- given
  (hs : IsChain (· ≤ ·) (s : Set α)) :
-- imply
  s.card ≤ maxChainSize α := by
-- proof
  apply MathlibExt.Combinatorics.Order.FinitePosets.card_le_maxChainSize s hs

/--
[exists_chain_card_eq_maxChainSize](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/FinitePosets.lean)
-/
@[path]
private lemma exists_chain_card_eq_maxChainSize_eq
  [Fintype α] [PartialOrder α] :
-- imply
  ∃ s : Finset α, IsChain (· ≤ ·) (s : Set α) ∧ s.card = maxChainSize α := by
-- proof
  apply MathlibExt.Combinatorics.Order.FinitePosets.exists_chain_card_eq_maxChainSize

/--
[minAntichainCoverSize_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/FinitePosets.lean)
-/
@[path]
private lemma minAntichainCoverSize_le_card_eq
  [Fintype α] [PartialOrder α]
  {C : Finset (Finset α)}
-- given
  (hC : IsAntichainCoverFin C) :
-- imply
  minAntichainCoverSize α ≤ C.card := by
-- proof
  apply MathlibExt.Combinatorics.Order.FinitePosets.minAntichainCoverSize_le_card C hC

/--
[exists_antichainCover_card_eq_minAntichainCoverSize](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/FinitePosets.lean)
-/
@[path]
private lemma exists_antichainCover_card_eq_minAntichainCoverSize_eq
  [Fintype α] [PartialOrder α] :
-- imply
  ∃ C : Finset (Finset α), IsAntichainCoverFin C ∧ C.card = minAntichainCoverSize α := by
-- proof
  apply MathlibExt.Combinatorics.Order.FinitePosets.exists_antichainCover_card_eq_minAntichainCoverSize

/--
[mirsky_dual_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/FinitePosets.lean)
-/
@[path]
private lemma mirsky_dual_general_eq
  [Fintype α] [PartialOrder α] :
-- imply
  maxChainSize α = minAntichainCoverSize α := by
-- proof
  apply MathlibExt.Combinatorics.Order.FinitePosets.mirsky_dual_general

/--
[mirsky_dual](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/FinitePosets.lean)
-/
@[path]
private lemma mirsky_dual_eq
  [Fintype α] [DecidableEq α] [PartialOrder α] :
-- imply
  maxChainSize α = minAntichainCoverSize α := by
-- proof
  apply MathlibExt.Combinatorics.Order.FinitePosets.mirsky_dual


-- created on 2026-10-20
