import Initialize.Tactic.Attr.Basic


-- define the circled plus operator
class OPlus (α : Type u) where
  oplus : α → α → α
  associative : ∀ x y z : α, oplus (oplus x y) z = oplus x (oplus y z)

