import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Graph.CompleteBipartiteCrossing
open MetaMathlibExt


/--
[legendre_regular_crossing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/CompleteBipartiteCrossing.lean)
-/
@[path]
private lemma legendre_regular_crossing_eq
  :
-- imply
  ∀ (n : ℕ),
    Finset.card
    (Finset.image
    (fun p => match p with
    | ((i, j), (i', j')) =>
    (((i' : Rat) - (i : Rat)) /
    (((i' : Rat) - (i : Rat)) + ((j : Rat) - (j' : Rat))),
    (i : Rat) +
    (((i' : Rat) - (i : Rat)) /
    (((i' : Rat) - (i : Rat)) +
    ((j : Rat) - (j' : Rat))) *
    ((j : Rat) - (i : Rat)))))
    (Finset.filter
    (fun p => match p with
    | ((i, j), (i', j')) => i < i' ∧ j' < j)
    (Finset.product
    (Finset.product (Finset.range n) (Finset.range n))
    (Finset.product (Finset.range n) (Finset.range n))))) =
    ((∑ a ∈ Finset.filter (fun a => 1 ≤ a) (Finset.range n),
    ∑ b ∈ Finset.filter (fun b => 1 ≤ b ∧ Nat.Coprime a b)
    (Finset.range n),
    (n - a) * (n - b)) -
    (∑ a ∈ Finset.filter (fun a => 1 ≤ 2 * a ∧ 2 * a < n)
    (Finset.range n),
    ∑ b ∈ Finset.filter
    (fun b => 1 ≤ 2 * b ∧ 2 * b < n ∧ Nat.Coprime a b)
    (Finset.range n),
    (n - 2 * a) * (n - 2 * b))) := by
-- proof
  apply MetaMathlibExt.legendre_regular_crossing


-- created on 2026-10-20
