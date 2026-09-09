import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetGetSlice.eq.Get_Add.of.GtSubMin
import Lemma.List.LengthSlice.eq.SubMin
import Lemma.Nat.CoeAdd.eq.AddCoeS
import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.Length.eq.Get_0.of.GtLength_0
import sympy.tensor.stack
import sympy.tensor.tensor
open Tensor List Bool Nat


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GetSlice.as.Stack.of.LeAdd |
| cast | Tensor.GetSlice.eq.Cast_Stack |
-/
@[main, cast]
private lemma main
  {m n j : ℕ}
-- given
  (h : j + n ≤ m)
  (X : Tensor α (m :: s)) :
-- imply
  X[j : j + n] ≃ [i < n] X[j + (i : ℕ)]'(Nat.lt_of_lt_of_le (Nat.add_lt_add_left i.isLt j) h) := by
-- proof
  have hm : X.length = m := Length.eq.Get_0.of.GtLength_0 (by simp) X
  have hlen : (⟨j, j + n, 1⟩ : Slice).length X.length = n := by
    simp only [hm]
    rw [AddCoeS.eq.CoeAdd (α := ℤ)]
    rw [LengthSlice.eq.SubMin]
    simp [Nat.min_eq_left h]
  apply SEq.of.All_SEqGetS.Eq.Eq hlen rfl
  intro i
  have hi : (i : ℕ) < (j + n) ⊓ m - j := by
    simpa [hlen, Nat.min_eq_left h] using i.isLt
  have hget := GetGetSlice.eq.Get_Add.of.GtSubMin (m := m) (n := j + n) (j := j) hi X
  apply SEq.of.Eq
  refine hget.trans ?_
  symm
  apply EqGetStack.fin


-- created on 2020-03-12
-- updated on 2026-09-09
