import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.Units
open scoped NumberField
open NumberField.InfinitePlace
open NumberField.Units


/--
[finiteIndex_closure_range_of_lt_one_off_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/Units.lean)
-/
@[path]
private lemma finiteIndex_closure_range_of_lt_one_off_diagonal_eq
  [Field F] [NumberField F]
  {u : NumberField.InfinitePlace F → (𝓞 F)ˣ}
-- given
  (hu : ∀ v w : NumberField.InfinitePlace F, w ≠ v → w (u v) < 1) :
-- imply
  (Subgroup.closure (Set.range u)).FiniteIndex := by
-- proof
  apply NumberField.Units.finiteIndex_closure_range_of_lt_one_off_diagonal u hu


-- created on 2026-10-20
