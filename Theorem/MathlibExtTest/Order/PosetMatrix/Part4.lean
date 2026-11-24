module
public import Def.Order.PosetMatrix
public import Theorem.Set.PosetMatrix
public import Mathlib.Tactic.FinCases
public import Def.MathlibExtTest.Order.PosetMatrix.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Order/PosetMatrix.lean -/
namespace MetaMathlibExt

example : ¬ IsPosetMatrix 3 badMat := by
  intro h
  have h01 : badMat 0 1 = true := rfl
  have h12 : badMat 1 2 = true := rfl
  have h02f : badMat 0 2 = false := rfl
  have h02t : badMat 0 2 = true :=
    IsPosetMatrix.transitive h 0 1 2 h01 h12
  rw [h02f] at h02t
  exact Bool.false_ne_true h02t

end MetaMathlibExt
