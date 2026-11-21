import Theorem.Nat.LtDiv.of.Lt_Mul
import Lemma.Vector.GetFlatten_AddMul.eq.Get
open Nat Vector


@[path]
private lemma main
-- given
  (h_t : t < m * n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  v.flatten.get ⟨t, by grind⟩ = (v.get ⟨t / n, LtDiv.of.Lt_Mul h_t⟩).get ⟨t % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h_t))⟩ := by
-- proof
  have := GetFlatten_AddMul.eq.Get.fin v ⟨t / n, LtDiv.of.Lt_Mul h_t⟩ ⟨t % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (by rintro rfl; simp at h_t))⟩
  simp at this
  rw [← this]
  congr 1
  simp [EqAddMulDiv]


-- created on 2026-07-13
-- updated on 2026-11-20
