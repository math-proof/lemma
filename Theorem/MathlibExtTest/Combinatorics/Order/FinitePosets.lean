/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Order/FinitePosets.lean -/


import Def.Combinatorics.Order.FinitePosets
import Lemma.Finset.Order.FinitePosets
import Mathlib.Tactic
open MathlibExt.Combinatorics.Order.FinitePosets


/-- The migrated theorem retains the exact former Wanted signature. -/
example {α : Type*} [Fintype α] [DecidableEq α] [PartialOrder α] :
    maxChainSize α = minAntichainCoverSize α :=
  mirsky_dual

/-- Every chain is no larger than every antichain cover. -/
example {α : Type*} [Fintype α] [PartialOrder α] (s : Finset α)
    (C : Finset (Finset α)) (hs : IsChain (· ≤ ·) (s : Set α)) (hC : IsAntichainCoverFin C) :
    s.card ≤ C.card :=
  (card_le_maxChainSize s hs).trans
    (mirsky_dual_general.trans_le (minAntichainCoverSize_le_card C hC))

/-- In the linear order `Fin 3`, the whole type is the longest chain. -/
example : maxChainSize (Fin 3) = 3 := by
  obtain ⟨s, -, hs⟩ := exists_chain_card_eq_maxChainSize (α := Fin 3)
  refine le_antisymm ?_ ?_
  · rw [← hs]
    exact (Finset.card_le_univ s).trans_eq (Fintype.card_fin 3)
  · simpa using card_le_maxChainSize (Finset.univ : Finset (Fin 3))
      fun a _ b _ _ => le_total a b

/-- Mirsky's theorem then says `Fin 3` needs three antichains. -/
example : minAntichainCoverSize (Fin 3) = 3 := by
  rw [← mirsky_dual]
  obtain ⟨s, -, hs⟩ := exists_chain_card_eq_maxChainSize (α := Fin 3)
  refine le_antisymm ?_ ?_
  · rw [← hs]
    exact (Finset.card_le_univ s).trans_eq (Fintype.card_fin 3)
  · simpa using card_le_maxChainSize (Finset.univ : Finset (Fin 3))
      fun a _ b _ _ => le_total a b

