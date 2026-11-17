module

public import Mathlib
public import Def.NumberTheory.RothAuxiliary.Part3

public section

open MathlibExt.NumberTheory.RothAuxiliary


/--
[rothMvWeight_add](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
public theorem Fin.RothMvWeightAdd.eq.AddRothSMvWeight.of.RothMvIndex
  {m : ℕ}
  (r : Fin m → ℕ) (i j : RothMvIndex m) :
-- imply
  rothMvWeight r (i + j) = rothMvWeight r i + rothMvWeight r j := by
-- proof
  simp only [rothMvWeight, Finsupp.add_apply, Nat.cast_add, add_div,
    Finset.sum_add_distrib]


-- updated on 2026-11-13
-- created on 2026-10-21
