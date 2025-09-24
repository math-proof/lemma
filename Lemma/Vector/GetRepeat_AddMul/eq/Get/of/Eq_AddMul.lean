import Lemma.Algebra.AddMul.lt.Mul
import Lemma.Vector.GetRepeat.eq.Get_Mod
import Lemma.Algebra.EqMod
open Algebra Vector


@[main]
private lemma fin
  {i : Fin m}
  {j : Fin n}
-- given
  (h_t : t = i * n + j)
  (v : List.Vector α n) :
-- imply
  have h_t : t < m * n := by convert AddMul.lt.Mul i j
  (v.repeat m).get ⟨t, h_t⟩ = v.get j := by
-- proof
  simp [GetRepeat.eq.Get_Mod.fin]
  simp [h_t]
  simp [EqMod]


@[main]
private lemma main
  {i : Fin m}
  {j : Fin n}
-- given
  (h_t : t = i * n + j)
  (v : List.Vector α n) :
-- imply
  have : t < m * n := by convert AddMul.lt.Mul i j
  (v.repeat m)[t] = v[j] := by
-- proof
  apply fin
  assumption


-- created on 2025-09-24
