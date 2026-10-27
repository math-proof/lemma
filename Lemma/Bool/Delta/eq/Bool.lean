import Def.Analysis.SpecialFunctions.TensorFunctions
import Initialize.Tactic.Attr.Basic


/--
| attributes | lemma |
| :---: | :---: |
| path | Bool.Delta.eq.Bool |
| comm | Bool.Bool.eq.Delta |
-/
@[path, comm]
private lemma main
  [DecidableEq α]
-- given
  (x y : α) :
-- imply
  KroneckerDelta x y = Bool.toNat (x = y) := by
-- proof
  simp [KroneckerDelta]


-- created on 2023-08-20
