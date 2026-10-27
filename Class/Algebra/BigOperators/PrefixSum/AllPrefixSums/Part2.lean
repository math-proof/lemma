import Initialize.Tactic.Attr.Basic
import Notation.Algebra.BigOperators.PrefixSum.AllPrefixSums


-- define the circled times operator
class OTimes (α : Type u) [OPlus α] where
  otimes : α → α → α
  distributive : ∀ a b c : α, otimes (a ⊕ b) c = (otimes a c) ⊕ (otimes b c)

