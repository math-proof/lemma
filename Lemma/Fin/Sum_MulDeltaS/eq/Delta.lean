import Lemma.Nat.Delta.eq.Ite
import sympy.functions.special.tensor_functions
open Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Fin.Sum_MulDeltaS.eq.Delta |
| comm | Fin.Delta.eq.Sum_MulDeltaS |
-/
@[main, comm]
private lemma main
  [Semiring α]
-- given
  (i j : Fin d) :
-- imply
  ∑ u : Fin d, (KroneckerDelta u i : α) * (KroneckerDelta u j : α) = (KroneckerDelta i j : α) := by
-- proof
  refine Eq.trans (Finset.sum_eq_single i ?off ?mem) ?_
  ·
    intro u _ hu
    simp [Delta.eq.Ite, hu]
  ·
    grind
  ·
    simp [Delta.eq.Ite]


-- created on 2026-09-02
