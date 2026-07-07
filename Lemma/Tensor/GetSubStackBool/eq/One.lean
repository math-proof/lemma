import Lemma.Int.Sub0.eq.Neg
import Lemma.Tensor.EqGet1_1
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetSub.eq.SubGetS
import sympy.tensor.functions
import sympy.tensor.stack
open Tensor Int


@[main]
private lemma main
  [AddGroupWithOne α]
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (i j : Fin n) :
-- imply
  let mask : Tensor α [n, n] := [i < n] [j < n] (Bool.toNat (p i j))
  ((mask - 1).get i).get j = if p i j then
    0
  else
    -1 := by
-- proof
  intro mask
  subst mask
  rw [GetSub.eq.SubGetS.fin]
  rw [EqGetStack.fn.fin]
  erw [GetSub.eq.SubGetS.fin]
  rw [EqGetStack.fn.fin]
  rw [EqGet1_1.fin]
  erw [EqGet1_1.fin]
  split_ifs with h
  .
    simp [h]
    erw [Nat.Sub.eq.Zero]
    rfl
  .
    simp [h]
    erw [Sub0.eq.Neg]
    rfl



-- created on 2025-12-23
