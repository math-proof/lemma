/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/


import Def.Order.PosetMatrix
import Lemma.Set.PosetMatrix
import Mathlib.Tactic.FinCases
import Def.MathlibExtTest.Order.PosetMatrix.Part3


namespace MetaMathlibExt

example : twoMat 1 0 = false :=
  IsPosetMatrix.upper twoMat_ok 1 0 (by decide)

example : twoMat 1 1 = true :=
  IsPosetMatrix.diagonal twoMat_ok 1

example : twoMat 0 1 = true :=
  IsPosetMatrix.transitive twoMat_ok 0 0 1 rfl rfl

example : IsPosetMatrix.Rel twoMat 0 0 :=
  IsPosetMatrix.rel_refl twoMat_ok 0

example : IsPosetMatrix.Rel twoMat 0 0 :=
  IsPosetMatrix.rel_trans twoMat_ok 0 0 0
    (IsPosetMatrix.rel_refl twoMat_ok 0)
    (IsPosetMatrix.rel_refl twoMat_ok 0)

end MetaMathlibExt
