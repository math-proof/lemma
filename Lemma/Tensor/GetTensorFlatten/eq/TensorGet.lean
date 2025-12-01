import sympy.tensor.tensor
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.DataGet.eq.Get.of.EqData_Flatten
import Lemma.Bool.EqUFnS.of.Eq
open Tensor Bool


@[main]
private lemma main
-- given
  (v : List.Vector (List.Vector α s.prod) n)
  (i : Fin n) :
-- imply
  (⟨v.flatten⟩ : Tensor α (n :: s))[i] = ⟨v[i]⟩ := by
-- proof
  let X : Tensor α (n :: s) := ⟨v.flatten⟩
  have h_t : X = ⟨v.flatten⟩ := rfl
  rw [← h_t]
  apply Eq.of.EqDataS
  simp
  have h_eq := EqUFnS.of.Eq h_t (·.data)
  simp at h_eq
  have := DataGet.eq.Get.of.EqData_Flatten h_eq i
  aesop


@[main]
private lemma fin
-- given
  (v : List.Vector (List.Vector α s.prod) n)
  (i : Fin n) :
-- imply
  (⟨v.flatten⟩ : Tensor α (n :: s)).get i = ⟨v.get i⟩ := by
-- proof
  apply main


-- created on 2025-05-24
-- updated on 2025-05-27
