import Mathlib
import sympy.Basic


/--
[IsAddCyclic_of_squarefree_natCard](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsAddCyclic_of_squarefree_natCard.lean)
-/
@[path]
private lemma main
  [AddCommGroup A]
-- given
  (hA : Squarefree (Nat.card A)) :
-- imply
  IsAddCyclic A := by
-- proof
  have : Finite A := Nat.finite_of_card_ne_zero hA.ne_zero
  rw [← isCyclic_multiplicative_iff]
  have hM : Squarefree (Nat.card (Multiplicative A)) := by
    rwa [Nat.card_congr Multiplicative.toAdd]
  have : IsZGroup (Multiplicative A) := IsZGroup.of_squarefree hM
  exact IsCyclic.of_exponent_eq_card (IsZGroup.exponent_eq_card (Multiplicative A))


-- created on 2026-10-03
