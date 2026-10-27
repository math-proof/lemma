import Lemma.Int.Sub0.eq.Neg
import Lemma.Nat.Sub.eq.Zero
import Lemma.Tensor.EqGet1_1
import Lemma.Tensor.GetSub.eq.SubGetS
import Theorem.Data.Holor.Functions
import Def.Data.Holor.Stack.Part2
open Tensor Int Nat
set_option maxHeartbeats 1000000


attribute [local irreducible] List.prod

@[path]
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
  rw [EqGetStack.fin]
  erw [GetSub.eq.SubGetS.fin]
  rw [EqGetStack.fin]
  erw [EqGet1_1.fin]
  erw [EqGet1_1.fin]
  split_ifs with h
  .
    simp [h]
    erw [Sub.eq.Zero]
    rfl
  .
    simp [h]
    erw [Sub0.eq.Neg]
    rfl


-- created on 2025-12-23
-- updated on 2026-10-26
