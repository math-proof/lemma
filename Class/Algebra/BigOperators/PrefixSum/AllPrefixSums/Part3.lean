import sympy.Basic
import Notation.Algebra.BigOperators.PrefixSum.AllPrefixSums.Part2


-- define the circled dot operator, the companion operator of ⊗
class ODot (α : Type u) [OPlus α] [OTimes α] where
  odot : α → α → α
  semiassociative : ∀ x y z : α, ((x ⊗ y) ⊗ z) = (x ⊗ (odot y z))
  associative : ∀ x y z : α, odot (odot x y) z = odot x (odot y z)

