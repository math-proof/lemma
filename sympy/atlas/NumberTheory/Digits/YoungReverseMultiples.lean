/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/YoungReverseMultiples.lean -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Ring

section
namespace MetaMathlibExt

private inductive IsCarryChain (g k : ℕ) : List ℕ → List ℕ → List ℕ → Prop
  | nil (c : ℕ) : IsCarryChain g k [] [] [c]
  | cons (x y c₀ c₁ : ℕ) (xs ys cs : List ℕ) :
      k * x + c₀ = y + c₁ * g →
      IsCarryChain g k xs ys (c₁ :: cs) →
      IsCarryChain g k (x :: xs) (y :: ys) (c₀ :: c₁ :: cs)

private def buildDigits (g k : ℕ) : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: xs, c₀ => ((k * x + c₀) % g) :: buildDigits g k xs ((k * x + c₀) / g)

private def buildCarries (g k : ℕ) : List ℕ → ℕ → List ℕ
  | [], c₀ => [c₀]
  | x :: xs, c₀ => c₀ :: buildCarries g k xs ((k * x + c₀) / g)

private def labelsOf (D : List ℕ) : List (ℕ × ℕ) :=
  List.zip (D.take (D.length / 2)) (D.reverse.take (D.length / 2))

private def carriesOf (g k : ℕ) (D : List ℕ) : List ℕ :=
  buildCarries g k D.reverse 0

private def nodesOf (g k : ℕ) (D : List ℕ) : List (ℕ × ℕ) :=
  List.zip ((carriesOf g k D).reverse.take (D.length / 2 + 1))
    ((carriesOf g k D).take (D.length / 2 + 1))

private def reconEven (labels : List (ℕ × ℕ)) : List ℕ :=
  (labels.map Prod.fst) ++ (labels.map Prod.snd).reverse

private def reconOdd (labels : List (ℕ × ℕ)) (mid : ℕ) : List ℕ :=
  (labels.map Prod.fst) ++ [mid] ++ (labels.map Prod.snd).reverse
end MetaMathlibExt
end
