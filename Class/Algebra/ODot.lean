module

public import Initialize.Tactic.Attr.Basic
public import Notation.Algebra.BigOperators.PrefixSum.AllPrefixSums.Part2
public section


-- define the circled dot operator, the companion operator of ⊗
class ODot (α : Type u) [OPlus α] [OTimes α] where
  odot : α → α → α
  semiassociative : ∀ x y z : α, ((x ⊗ y) ⊗ z) = (x ⊗ (odot y z))
