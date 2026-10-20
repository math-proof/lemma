import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MultipleZeta.Reversal
open MetaMathlibExt.MultipleZeta


/--
[Index.reverse_entries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma Index_reverse_entries_eq
  {index : Index} :
-- imply
  index.reverse.entries = index.entries.reverse := by
-- proof
  apply MetaMathlibExt.MultipleZeta.Index.reverse_entries index

/--
[Index.reverse_weight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma Index_reverse_weight_eq
  {index : Index} :
-- imply
  index.reverse.weight = index.weight := by
-- proof
  apply MetaMathlibExt.MultipleZeta.Index.reverse_weight index

/--
[Index.reverse_depth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma Index_reverse_depth_eq
  {index : Index} :
-- imply
  index.reverse.depth = index.depth := by
-- proof
  apply MetaMathlibExt.MultipleZeta.Index.reverse_depth index

/--
[Index.reverse_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma Index_reverse_reverse_eq
  {index : Index} :
-- imply
  index.reverse.reverse = index := by
-- proof
  apply MetaMathlibExt.MultipleZeta.Index.reverse_reverse index

/--
[Index.isIncreasingAdmissible_iff_reverse_isAdmissible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma Index_isIncreasingAdmissible_iff_reverse_isAdmissible_eq
  {index : Index} :
-- imply
  index.IsIncreasingAdmissible ↔ index.reverse.IsAdmissible := by
-- proof
  apply MetaMathlibExt.MultipleZeta.Index.isIncreasingAdmissible_iff_reverse_isAdmissible index

/--
[Index.reverse_entry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma Index_reverse_entry_eq
  {index : Index}
  {i : Fin index.reverse.depth} :
-- imply
  index.reverse.entry i =
    index.entry (Fin.rev (Fin.castOrderIso index.reverse_depth i)) := by
-- proof
  apply MetaMathlibExt.MultipleZeta.Index.reverse_entry index i

/--
[increasingEquivDecreasing_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma increasingEquivDecreasing_apply_eq
  {index : Index}
  {m : StrictIncreasingTuple index.depth}
  {i : Fin index.reverse.depth} :
-- imply
  (increasingEquivDecreasing index m).1 i =
    m.1 (Fin.rev (Fin.castOrderIso index.reverse_depth i)) := by
-- proof
  apply MetaMathlibExt.MultipleZeta.increasingEquivDecreasing_apply index m i

/--
[increasingSummand_eq_strictSummand_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma increasingSummand_eq_strictSummand_reverse_eq
  {index : Index}
  {m : StrictIncreasingTuple index.depth} :
-- imply
  increasingSummand index m =
    strictSummand index.reverse (increasingEquivDecreasing index m) := by
-- proof
  apply MetaMathlibExt.MultipleZeta.increasingSummand_eq_strictSummand_reverse index m

/--
[increasingValue_eq_strictValue_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma increasingValue_eq_strictValue_reverse_eq
  {index : Index}
-- given
  (h : index.IsIncreasingAdmissible) :
-- imply
  increasingValue index h =
    strictValue index.reverse
    (Or.inl (index.isIncreasingAdmissible_iff_reverse_isAdmissible.mp h)) := by
-- proof
  apply MetaMathlibExt.MultipleZeta.increasingValue_eq_strictValue_reverse index h


-- created on 2026-10-20
