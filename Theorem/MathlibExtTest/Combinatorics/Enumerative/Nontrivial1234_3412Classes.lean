/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/Nontrivial1234_3412Classes.lean -/


import Theorem.Combinatorics.Enumerative.Nontrivial1234_3412Classes.Part21
import Lemma.Finset.Enumerative.Nontrivial1234_3412Classes
import Mathlib.Tactic.NormNum


namespace MetaMathlibExt

-- The closed formula gives 51 nontrivial classes in `S₇`.
example :
    let OneMove : Equiv.Perm (Fin 7) → Equiv.Perm (Fin 7) → Prop :=
      fun σ τ => ∃ i1 i2 i3 i4 : Fin 7,
        i1.val < i2.val ∧ i2.val < i3.val ∧ i3.val < i4.val ∧
          σ i1 < σ i2 ∧ σ i2 < σ i3 ∧ σ i3 < σ i4 ∧
          τ i1 = σ i3 ∧ τ i2 = σ i4 ∧ τ i3 = σ i1 ∧ τ i4 = σ i2 ∧
          ∀ j : Fin 7, j ≠ i1 → j ≠ i2 → j ≠ i3 → j ≠ i4 → τ j = σ j
    Nat.card { C : Set (Equiv.Perm (Fin 7)) //
        ∃ σ, C = { τ | Relation.EqvGen OneMove σ τ } ∧ 1 < Nat.card ↑C } = 51 := by
  simpa using card_nontrivial_1234_3412_classes 7 (by norm_num)

end MetaMathlibExt
