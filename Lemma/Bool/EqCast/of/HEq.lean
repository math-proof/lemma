import Lemma.Bool.Eq.of.HEq
import Lemma.Bool.HEq.is.EqCast.of.Eq
open Bool


/--
| attributes | lemma |
| :---: | :---: |
| main | Bool.EqCast.of.HEq |
| comm 1 | Bool.Eq_Cast.of.HEq |
-/
@[main, comm 1]
private lemma main
  {a : α}
  {b : β}
-- given
  (h : HEq a b) :
-- imply
  cast (Eq.of.HEq h) a = b :=
-- proof
  EqCast.of.HEq.Eq (Eq.of.HEq h) h


-- created on 2025-07-16
