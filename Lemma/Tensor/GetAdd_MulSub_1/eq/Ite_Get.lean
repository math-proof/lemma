import Lemma.Tensor.Get.eq.Zero.of.Eq_0
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetMul.eq.MulGet.of.Lt_Get_0.GtLength_0
import sympy.core.relational
import sympy.tensor.functions
import sympy.tensor.stack
open Tensor


@[main]
private lemma main
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (A : Tensor ℝ* [n, n])
  (i j : Fin n) :
-- imply
  let mask : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (p i j))
  (A + (mask - 1) * Hyperreal.omega)[i, j] = if p i j then
    A[i, j]
  else
    (-Hyperreal.omega : Tensor ℝ* []) := by
-- proof
  intro mask
  denote h_A : A' = A + (mask - 1) * Hyperreal.omega
  simp [GetElem.getElem]
  repeat rw [GetAdd.eq.AddGetS.fin]
  split_ifs with h_p
  ·
    have := GetMul.eq.MulGet.of.Lt_Get_0.GtLength_0.fin (by grind) (by grind) (mask - 1) Hyperreal.omega (i := i)
    simp at this
    rw [this]
    simp
    have := GetMul.eq.MulGet.of.Lt_Get_0.GtLength_0.fin (by grind) (by grind) ((mask - 1).get i) Hyperreal.omega (i := j)
    simp at this
    rw [this]
    -- apply Get.eq.Zero.of.Eq_0.fin
    sorry
  ·
    sorry


-- created on 2025-12-06
