import Initialize.Tactic.Attr.Basic


-- define the circled plus operator
class OPlus (α : Type u) where
  oplus : α → α → α
