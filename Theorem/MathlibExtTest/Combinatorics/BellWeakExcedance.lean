/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/BellWeakExcedance.lean -/


import Def.Combinatorics.BellWeakExcedance.Part11
import Lemma.Finset.BellWeakExcedance


-- The weak-excedance count for n = 3 is 5.
example :
    Fintype.card { σ : Equiv.Perm (Fin 3) //
      ∀ i j : Fin 3, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j } = 5 := by
  rw [MetaMathlibExt.bell_count_perm_increasing_weakExcedance_letters]
  simp [Nat.bell_succ, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ]

-- The weak-excedance count for n = 4 is 15.
example :
    Fintype.card { σ : Equiv.Perm (Fin 4) //
      ∀ i j : Fin 4, i < j → i ≤ σ i → j ≤ σ j → σ i < σ j } = 15 := by
  rw [MetaMathlibExt.bell_count_perm_increasing_weakExcedance_letters]
  simp [Nat.bell_succ, ← Nat.range_succ_eq_Iic, Finset.sum_range_succ]

