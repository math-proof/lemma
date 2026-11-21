import Instance.Data.Tensor.Defs.Part2


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.Cast_Mul.eq.MulCastS.of.Eq |
| comm | Tensor.MulCastS.eq.Cast_Mul.of.Eq |
-/
@[path, comm]
private lemma main
  [Mul α]
-- given
  (h : s = s')
  (A B : Tensor α s) :
-- imply
  have h := congrArg (Tensor α) h
  cast h (A * B) = cast h A * cast h B := by
-- proof
  subst s'
  rfl


-- created on 2025-12-01
-- updated on 2026-11-20
