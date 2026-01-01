import sympy.vector.Basic
import Lemma.Nat.Ne_0
import Lemma.Nat.Ne_0.of.Mul.ne.Zero
import Lemma.Nat.LtMod.of.Ne_0
import Lemma.Nat.Any_Eq_AddMul
import Lemma.Vector.GetFlatten_AddMul.eq.Get
import Lemma.Nat.EqMod
open Vector Nat


@[main, fin, val]
private lemma main
-- given
  (x : List.Vector α n)
  (k : Fin (m * n)) :
-- imply
  (x.repeat m)[k] = x[k % n]'(LtMod.of.Ne_0 (Ne_0.of.Mul.ne.Zero (Ne_0 k)) k) := by
-- proof
  let ⟨i, j, h_ij⟩ := Any_Eq_AddMul k
  unfold List.Vector.repeat
  simp [h_ij]
  simp [GetElem.getElem]
  rw [GetFlatten_AddMul.eq.Get.fin]
  simp [EqMod]


-- created on 2025-09-24
