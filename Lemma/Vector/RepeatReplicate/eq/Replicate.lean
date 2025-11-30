import Lemma.Vector.GetRepeat.eq.Get_Mod
import sympy.vector.Basic
open Vector


@[main]
private lemma main
-- given
  (m n : ℕ)
  (x : α) :
-- imply
  (List.Vector.replicate n x).repeat m = List.Vector.replicate (m * n) x := by
-- proof
  ext i
  simp [GetRepeat.eq.Get_Mod.fin]


-- created on 2025-11-30
