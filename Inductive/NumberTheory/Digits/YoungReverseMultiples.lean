/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/YoungReverseMultiples.lean -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Ring


section

namespace MetaMathlibExt

inductive IsCarryChain (g k : ℕ) : List ℕ → List ℕ → List ℕ → Prop
  | nil (c : ℕ) : IsCarryChain g k [] [] [c]
  | cons (x y c₀ c₁ : ℕ) (xs ys cs : List ℕ) :
      k * x + c₀ = y + c₁ * g →
      IsCarryChain g k xs ys (c₁ :: cs) →
      IsCarryChain g k (x :: xs) (y :: ys) (c₀ :: c₁ :: cs)

end MetaMathlibExt
end
