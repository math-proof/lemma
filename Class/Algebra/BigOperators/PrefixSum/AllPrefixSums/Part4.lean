import Initialize.Tactic.Attr.Basic
import Def.Algebra.BigOperators.PrefixSum.AllPrefixSums


class Bullet (α : Type u) [OPlus α] [OTimes α] [ODot α] where
  bullet : α × α → α × α → α × α
  property : ∀ cᵢ c_j : α × α, bullet cᵢ c_j = ⟨cᵢ.fst ⊙ c_j.fst, (cᵢ.snd ⊗ c_j.fst) ⊕ c_j.snd⟩

