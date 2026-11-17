/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/YoungReverseMultiples.lean -/

module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.List.Basic
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Tactic.Ring


section

namespace MetaMathlibExt

public inductive IsCarryChain (g k : ℕ) : List ℕ → List ℕ → List ℕ → Prop
  | nil (c : ℕ) : IsCarryChain g k [] [] [c]
  | cons (x y c₀ c₁ : ℕ) (xs ys cs : List ℕ) :
      k * x + c₀ = y + c₁ * g →
      IsCarryChain g k xs ys (c₁ :: cs) →
      IsCarryChain g k (x :: xs) (y :: ys) (c₀ :: c₁ :: cs)

end MetaMathlibExt
end
