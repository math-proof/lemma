/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Index.lean -/

import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.PNat.Basic
import Def.NumberTheory.MultipleZeta.Index
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

/-- The bundled and list formulations of admissibility agree. -/
theorem Index.isAdmissible_iff (index : Index) :
    index.IsAdmissible ↔ MetaMathlibExt.MultipleZeta.IsAdmissible index.entries := by
  rcases index with ⟨_, c⟩
  cases hblocks : c.blocks with
  | nil => simp [Index.IsAdmissible, Index.entries, IsAdmissible, hblocks]
  | cons h t =>
      simp only [Index.IsAdmissible, Index.entries, IsAdmissible, hblocks]
      constructor
      · intro hh
        refine ⟨hh, fun x hx => c.blocks_pos ?_⟩
        simpa [hblocks] using List.mem_cons_of_mem h hx
      · exact fun h => h.1

end MetaMathlibExt.MultipleZeta
