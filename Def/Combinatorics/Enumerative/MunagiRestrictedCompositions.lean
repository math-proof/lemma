/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MunagiRestrictedCompositions.lean -/

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Tactic.Ring


namespace MetaMathlibExt

/-- Expand a block list for the forward map: each part `a` becomes `1`
followed by `(a - 1) / k` copies of `k`. -/
def expandA (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: as => 1 :: (List.replicate ((a - 1) / k) k ++ expandA k as)

/-- Expand a block list for the backward map: each part `b` becomes `k`
followed by `b - k` copies of `1`. -/
def expandB (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => k :: (List.replicate (b - k) 1 ++ expandB k bs)

/-- Parse a sequence by cutting before every occurrence of `X`, accumulating
the other elements into the current open part. -/
def parseAux (X cur : ℕ) : List ℕ → List ℕ
  | [] => [cur]
  | y :: ys => if y = X then cur :: parseAux X y ys else parseAux X (cur + y) ys

/-- Parse a nonempty sequence with `parseAux`, and `[]` to `[]`. -/
def parseBefore (X : ℕ) : List ℕ → List ℕ
  | [] => []
  | x :: xs => parseAux X x xs

/-- Forward block map: expand, replace the leading `1` by `k`, re-parse. -/
def fwd (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: as => parseBefore k (k :: (List.replicate ((a - 1) / k) k ++ expandA k as))

/-- Backward block map: expand, replace the leading `k` by `1`, re-parse. -/
def bwd (k : ℕ) : List ℕ → List ℕ
  | [] => []
  | b :: bs => parseBefore 1 (1 :: (List.replicate (b - k) 1 ++ expandB k bs))

end MetaMathlibExt
