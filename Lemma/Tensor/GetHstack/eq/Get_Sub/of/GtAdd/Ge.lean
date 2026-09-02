import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetHstack.eq.AppendGetS
open Tensor


@[main]
private lemma main
-- given
  (h₀ : j ≥ n)
  (h₁ : n + m > j)
  (A : Tensor α [d, n])
  (B : Tensor α [d, m])
  (i : Fin d) :
-- imply
  let h_j : j - n < m := by grind
  id (α := Tensor α []) (A.hstack B)[i][j] = id (α := Tensor α []) B[i][j - n] := by
-- proof
  intro
  apply (congrArg (fun t : Tensor α [n + m] => t[j]) (by simpa [id] using GetHstack.eq.AppendGetS A B i)).trans
  apply GetAppend.eq.Get_Sub.of.GtAdd.Ge h₀ h₁


-- created on 2026-09-01
-- updated on 2026-09-02
