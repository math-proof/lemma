/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Index.lean -/

import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.PNat.Basic
import Def.NumberTheory.MultipleZeta.Index.Part2
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

/-- Reading a Hoffman block as a list recovers `k - 1` copies of `x` followed
by one `y`. -/
@[simp]
theorem toList_hoffmanBlock (k : PNat) :
    FreeMonoid.toList (hoffmanBlock k) =
      List.replicate (k.val - 1) false ++ [true] := by
  simp [hoffmanBlock]

end MetaMathlibExt.MultipleZeta
