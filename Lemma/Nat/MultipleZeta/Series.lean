import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MultipleZeta.Series
open MetaMathlibExt.MultipleZeta


/--
[Index.empty_entries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
private lemma Index_empty_entries_eq
  :
-- imply
  Index.empty.entries = [] := by
-- proof
  apply MetaMathlibExt.MultipleZeta.Index.empty_entries

/--
[Index.empty_weight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
private lemma Index_empty_weight_eq
  :
-- imply
  Index.empty.weight = 0 := by
-- proof
  apply MetaMathlibExt.MultipleZeta.Index.empty_weight

/--
[Index.empty_depth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
private lemma Index_empty_depth_eq
  :
-- imply
  Index.empty.depth = 0 := by
-- proof
  apply MetaMathlibExt.MultipleZeta.Index.empty_depth

/--
[Index.entry_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
private lemma Index_entry_coe_eq
  {index : Index}
  {i : Fin index.depth} :
-- imply
  (index.entry i : ℕ) = index.2.blocksFun i := by
-- proof
  apply MetaMathlibExt.MultipleZeta.Index.entry_coe index i

/--
[StrictDecreasingTuple.eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
private lemma StrictDecreasingTuple_eq_empty_eq
  {m : StrictDecreasingTuple 0} :
-- imply
  m = StrictDecreasingTuple.empty := by
-- proof
  apply MetaMathlibExt.MultipleZeta.StrictDecreasingTuple.eq_empty m

/--
[strictSummand_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
private lemma strictSummand_empty_eq
  {m : StrictDecreasingTuple Index.empty.depth} :
-- imply
  strictSummand Index.empty m = 1 := by
-- proof
  apply MetaMathlibExt.MultipleZeta.strictSummand_empty m

/--
[strictValue_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
private lemma strictValue_empty_eq
-- given
  (h : Index.empty.IsAdmissibleOrEmpty) :
-- imply
  strictValue Index.empty h = 1 := by
-- proof
  apply MetaMathlibExt.MultipleZeta.strictValue_empty h

/--
[WeaklyDecreasingTuple.eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
private lemma WeaklyDecreasingTuple_eq_empty_eq
  {m : WeaklyDecreasingTuple 0} :
-- imply
  m = WeaklyDecreasingTuple.empty := by
-- proof
  apply MetaMathlibExt.MultipleZeta.WeaklyDecreasingTuple.eq_empty m

/--
[starSummand_toWeaklyDecreasing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
private lemma starSummand_toWeaklyDecreasing_eq
  {index : Index}
  {m : StrictDecreasingTuple index.depth} :
-- imply
  starSummand index m.toWeaklyDecreasing = strictSummand index m := by
-- proof
  apply MetaMathlibExt.MultipleZeta.starSummand_toWeaklyDecreasing index m

/--
[starSummand_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
private lemma starSummand_empty_eq
  {m : WeaklyDecreasingTuple Index.empty.depth} :
-- imply
  starSummand Index.empty m = 1 := by
-- proof
  apply MetaMathlibExt.MultipleZeta.starSummand_empty m

/--
[starValue_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
private lemma starValue_empty_eq
-- given
  (h : Index.empty.IsAdmissibleOrEmpty) :
-- imply
  starValue Index.empty h = 1 := by
-- proof
  apply MetaMathlibExt.MultipleZeta.starValue_empty h


-- created on 2026-10-20
