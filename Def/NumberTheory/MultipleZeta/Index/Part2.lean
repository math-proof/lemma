/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Index.lean -/

module

public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Combinatorics.Enumerative.Composition
public import Mathlib.Data.PNat.Basic
public import Theorem.NumberTheory.MultipleZeta.Index

@[expose] public section

/-!
# Multiple-zeta indices

This file defines multiple-zeta indices, admissibility for bundled and list
representations, and Hoffman blocks in a two-letter free monoid.

## Main definitions

* `MetaMathlibExt.MultipleZeta.Index`
* `MetaMathlibExt.MultipleZeta.Index.entries`
* `MetaMathlibExt.MultipleZeta.Index.weight`
* `MetaMathlibExt.MultipleZeta.Index.depth`
* `MetaMathlibExt.MultipleZeta.Index.height`
* `MetaMathlibExt.MultipleZeta.Index.IsAdmissible`
* `MetaMathlibExt.MultipleZeta.IsAdmissible`
* `MetaMathlibExt.MultipleZeta.hoffmanBlock`

## Main theorems

* `MetaMathlibExt.MultipleZeta.Index.isAdmissible_iff`
* `MetaMathlibExt.MultipleZeta.toList_hoffmanBlock`
-/


namespace MetaMathlibExt.MultipleZeta

/-- Hoffman block word `z_k = x ^ (k - 1) * y` for positive `k` in
`FreeMonoid Bool`, with `false` representing `x` and `true` representing `y`.
Source `2307.09867:D05`. -/
def hoffmanBlock (k : PNat) : FreeMonoid Bool :=
  FreeMonoid.ofList (List.replicate (k.val - 1) false ++ [true])

end MetaMathlibExt.MultipleZeta
