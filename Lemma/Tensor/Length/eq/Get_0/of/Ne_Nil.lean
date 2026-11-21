import Def.Data.Tensor.Defs
import Initialize.Tactic.Attr.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.Length.eq.Get_0.of.Ne_Nil |
| comm | Tensor.Get_0.eq.Length.of.Ne_Nil |
-/
@[path, comm]
private lemma main
-- given
  (h : s ≠ [])
  (X : Tensor α s) :
-- imply
  X.length = s.get ⟨0, List.length_pos_iff.mpr h⟩ := by
-- proof
  simp [Tensor.length]
  cases s
  ·
    contradiction
  ·
    cases X
    simp


-- created on 2025-10-10
-- updated on 2026-11-20
