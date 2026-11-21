import Instance.Data.Vector.Basic.Arithmetic
import Theorem.Data.Vector.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Vector.Zero.eq.Replicate |
| comm | Vector.Replicate.eq.Zero |
-/
@[path, comm]
private lemma main
  [Zero α] :
-- imply
  (0 : List.Vector α n) = List.Vector.replicate n 0 :=
-- proof
  rfl


-- created on 2025-06-22
-- updated on 2026-11-20
