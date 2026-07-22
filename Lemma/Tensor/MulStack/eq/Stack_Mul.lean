import Lemma.Fin.Any_Eq_AddMul.of.Lt_Mul
import Lemma.Nat.Mul
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Vector.GetFlatten.eq.Get.of.Eq_AddMul
open Fin Nat Tensor Vector


@[main]
private lemma scalar
  [Mul α]
-- given
  (X : Tensor α (n :: s))
  (a : α) :
-- imply
  ([i < n] X[i]) * a = [i < n] X[i] * a := by
-- proof
  unfold Stack Tensor.fromVector
  simp only [HMul.hMul]
  simp
  ext t
  have h_t := t.isLt
  let ⟨q, r, h_qr⟩ := Any_Eq_AddMul.of.Lt_Mul h_t
  simp [GetFlatten.eq.Get.of.Eq_AddMul.fin h_qr]


@[main]
private lemma main
  [Mul α]
-- given
  (g : Tensor α (n :: s))
  (f : ℕ → Tensor α s) :
-- imply
  ([i < n] f i) * g = [i < n] (
    let gi : Tensor α s := g[i]
    f i * gi) := by
-- proof
  simp
  apply Eq.of.All_EqGetS
  intro i
  rw [EqGetStack.fn]
  rw [@Tensor.GetMul.eq.MulGetS]
  rw [EqGetStack]
  rfl


@[main]
private lemma fin
  [Mul α]
-- given
  (g : Tensor α (n :: s))
  (f : Fin n → Tensor α s) :
-- imply
  ([i < n] f i) * g = [i < n] (
    let gi : Tensor α s := g[i]
    f i * gi) := by
-- proof
  if h : n = 0 then
    subst h
    apply Eq.of.All_EqGetS.fin
    intro t
    have h_t := t.isLt
    simp at h_t
  else
    have := main g (fun i => if h_i : i < n then
      f ⟨i, by grind⟩
    else
      f ⟨0, by grind⟩)
    simp at this
    grind


-- created on 2025-12-06
-- updated on 2026-07-22
