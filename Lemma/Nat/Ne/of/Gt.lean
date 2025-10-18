import Lemma.Nat.Ne.of.Lt
open Nat


/--
Given that `x > y` in a preorder, this lemma deduces that `x` and `y` are distinct.
It serves as the symmetric counterpart to `Ne.of.Lt`, utilizing the antisymmetry property inherent in the order relation to establish inequality.
-/
@[main]
private lemma main
  [Preorder α]
  {x y : α}
-- given
  (h : x > y) :
-- imply
  x ≠ y :=
-- proof
  (Ne.of.Lt h).symm


-- created on 2024-07-01
-- updated on 2025-04-04
