module
public import Initialize.Tactic.Attr.Basic


public section

@[path]
private theorem main
  [MulZeroClass α]
  {a : α} :
-- imply
  a * 0 = 0 := by
-- proof
  apply MulZeroClass.mul_zero


-- created on 2024-11-25
