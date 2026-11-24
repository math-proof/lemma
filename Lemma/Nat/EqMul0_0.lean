module
public import Initialize.Tactic.Attr.Basic


public section

@[path]
private lemma main
  [MulZeroClass α]
  {a : α} :
-- imply
  0 * a = 0 := by
-- proof
  apply MulZeroClass.zero_mul


-- created on 2024-11-25
