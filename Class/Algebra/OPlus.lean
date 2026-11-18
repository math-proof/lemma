module

public import Initialize.Tactic.Attr.Basic
public section


-- define the circled plus operator
class OPlus (α : Type u) where
  oplus : α → α → α
