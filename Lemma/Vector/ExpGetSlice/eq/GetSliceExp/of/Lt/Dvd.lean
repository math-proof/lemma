import Lemma.List.LengthSlice.eq.Div.of.Lt.Dvd
import Lemma.Vector.GetExp.eq.ExpGet
import Lemma.Vector.GetGetSlice.eq.Get.of.Lt.Lt.Dvd
import sympy.vector.functions
open Vector List


@[main]
private lemma main
  [Exp α]
  {i d : ℕ}
-- given
  (h_d : d ∣ n)
  (h_i : i < d)
  (x : List.Vector α n) :
-- imply
  exp x[i : n:d] = (exp x)[i : n:d] := by
-- proof
  ext t
  have h_t := t.isLt
  simp [LengthSlice.eq.Div.of.Lt.Dvd h_d h_i] at h_t
  rw [GetExp.eq.ExpGet.fin]
  repeat rw [GetGetSlice.eq.Get.of.Lt.Lt.Dvd h_d h_t h_i]
  rw [GetExp.eq.ExpGet.fin]


-- created on 2025-11-29
