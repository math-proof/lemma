/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Digits/YoungReverseMultiples.lean -/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Forall2
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic.Ring
import Inductive.NumberTheory.Digits.YoungReverseMultiples


section

namespace MetaMathlibExt

def buildDigits (g k : ℕ) : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: xs, c₀ => ((k * x + c₀) % g) :: buildDigits g k xs ((k * x + c₀) / g)

def buildCarries (g k : ℕ) : List ℕ → ℕ → List ℕ
  | [], c₀ => [c₀]
  | x :: xs, c₀ => c₀ :: buildCarries g k xs ((k * x + c₀) / g)

def labelsOf (D : List ℕ) : List (ℕ × ℕ) :=
  List.zip (D.take (D.length / 2)) (D.reverse.take (D.length / 2))

def carriesOf (g k : ℕ) (D : List ℕ) : List ℕ :=
  buildCarries g k D.reverse 0

def nodesOf (g k : ℕ) (D : List ℕ) : List (ℕ × ℕ) :=
  List.zip ((carriesOf g k D).reverse.take (D.length / 2 + 1))
    ((carriesOf g k D).take (D.length / 2 + 1))

def reconEven (labels : List (ℕ × ℕ)) : List ℕ :=
  (labels.map Prod.fst) ++ (labels.map Prod.snd).reverse

def reconOdd (labels : List (ℕ × ℕ)) (mid : ℕ) : List ℕ :=
  (labels.map Prod.fst) ++ [mid] ++ (labels.map Prod.snd).reverse

end MetaMathlibExt
end
