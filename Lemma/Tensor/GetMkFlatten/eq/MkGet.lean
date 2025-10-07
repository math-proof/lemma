import sympy.tensor.tensor
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.Get.eq.DataGet.of.Flatten.eq.Data
import Lemma.Bool.EqUFnS.of.Eq
open Tensor Bool


@[main]
private lemma main
-- given
  (v : List.Vector (List.Vector α s.prod) s₀)
  (i : Fin s₀) :
-- imply
  (⟨v.flatten⟩ : Tensor α (s₀ :: s))[i] = ⟨v[i]⟩ := by
-- proof
  let t : Tensor α (s₀ :: s) := ⟨v.flatten⟩
  have h_t : t = ⟨v.flatten⟩ := rfl
  rw [← h_t]
  apply Eq.of.EqDataS
  simp
  have h_eq := EqUFnS.of.Eq h_t (·.data)
  simp at h_eq
  have := Get.eq.DataGet.of.Flatten.eq.Data h_eq i
  aesop


-- created on 2025-05-24
-- updated on 2025-05-27
