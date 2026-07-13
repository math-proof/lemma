import Lemma.Nat.LtMod.of.Lt_Mul
import Lemma.Nat.LtDiv.of.Lt_Mul
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Vector.GetFlatten_AddMul.eq.Get
open Nat Vector


@[main]
private lemma main
-- given
  (h_t : t < m * n)
  (v : List.Vector (List.Vector α n) m) :
-- imply
  v.flatten.get ⟨t, by grind⟩ = (v.get ⟨t / n, Nat.LtDiv.of.Lt_Mul h_t⟩).get ⟨t % n, Nat.LtMod.of.Lt_Mul h_t⟩ := by
-- proof
  have := GetFlatten_AddMul.eq.Get.fin v ⟨t / n, Nat.LtDiv.of.Lt_Mul h_t⟩ ⟨t % n, Nat.LtMod.of.Lt_Mul h_t⟩
  simp at this
  rw [← this]
  congr 1
  simp [EqAddMulDiv]


-- created on 2026-07-13
