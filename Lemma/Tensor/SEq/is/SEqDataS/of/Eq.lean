import Lemma.Tensor.HEq.of.SEqDataS.Eq
import Lemma.Bool.SEq.is.Eq
open Tensor Bool


/--
| attributes | lemma |
| :---: | :---: |
| path | Tensor.SEq.is.SEqDataS.of.Eq |
| comm | Tensor.SEqDataS.is.SEq.of.Eq |
| mp | Tensor.SEqDataS.of.SEq.Eq |
| mpr | Tensor.SEq.of.SEqDataS.Eq |
-/
@[path, comm, mp, mpr]
private lemma main
  {A : Tensor α s}
  {B : Tensor α s'}
-- given
  (h_s : s = s') :
-- imply
  A ≃ B ↔ A.data ≃ B.data := by
-- proof
  subst h_s
  repeat rw [SEq.is.Eq]
  cases A
  cases B
  simp


-- created on 2025-06-29
-- updated on 2026-11-20
