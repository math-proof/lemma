import Lemma.Tensor.GetAdd_MulSub_1.eq.Ite_Get
import Lemma.Tensor.GetExp.eq.ExpGet
import Lemma.Tensor.Setoid.is.All_SetoidGetS.of.GtLength_0
import sympy.tensor.functions
import sympy.tensor.stack
open Tensor


@[main]
private lemma main
  {n : ℕ}
-- given
  (p : Fin n → Fin n → Bool)
  (A : Tensor ℝ [n, n]) :
-- imply
  let mask : Tensor ℝ* [n, n] := [i < n] [j < n] (Bool.toNat (p i j))
  let A : Tensor ℝ* [n, n] := A
  exp (A + (mask - 1) * Hyperreal.omega) ≈ exp A * mask := by
-- proof
  intro mask A'
  have h_A : A' = map Hyperreal.ofReal A := rfl
  apply Setoid.of.All_SetoidGetS.GtLength_0 (h := by simp)
  intro i
  apply Setoid.of.All_SetoidGetS.GtLength_0 (h := by simp)
  intro j
  simp
  have := GetExp.eq.ExpGet.fin (A' + (mask - 1) * Hyperreal.omega) ⟨i, by grind⟩
  simp at this
  rw [this]
  have := GetExp.eq.ExpGet.fin ((A' + (mask - 1) * Hyperreal.omega).get i) ⟨j, by grind⟩
  simp at this
  rw [this]
  have := GetAdd_MulSub_1.eq.Ite_Get.fin p A i j
  simp at this
  rw [← h_A] at this
  sorry


-- created on 2025-12-05
-- updated on 2025-12-24
