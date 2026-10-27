import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.MultipleZeta.Series.Part3
open MetaMathlibExt.MultipleZeta


namespace MetaMathlibExt.MultipleZeta

/--
[Index.empty_depth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
lemma Index.empty_depth
  :
-- imply
  Index.empty.depth = 0 :=
-- proof
  rfl

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[strictSummand_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
lemma strictSummand_empty
  {m : StrictDecreasingTuple Index.empty.depth} :
-- imply
  strictSummand Index.empty m = 1 := by
-- proof
  unfold strictSummand
  have hempty : (Finset.univ : Finset (Fin Index.empty.depth)) = ∅ := by
    ext i
    exact Fin.elim0 (Index.empty_depth ▸ i)
  rw [hempty]
  simp only [Finset.prod_empty, inv_one]

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[strictValue_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
lemma strictValue_empty
-- given
  (h : Index.empty.IsAdmissibleOrEmpty) :
-- imply
  strictValue Index.empty h = 1 := by
-- proof
  let m : StrictDecreasingTuple Index.empty.depth := by
    simpa only [Index.empty_depth] using StrictDecreasingTuple.empty
  unfold strictValue
  rw [tsum_eq_single m]
  · exact strictSummand_empty m
  · intro b hb
    exfalso
    apply hb
    apply Subtype.ext
    funext i
    exact Fin.elim0 (Index.empty_depth ▸ i)

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[starSummand_toWeaklyDecreasing](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
lemma starSummand_toWeaklyDecreasing
  {index : Index}
  {m : StrictDecreasingTuple index.depth} :
-- imply
  starSummand index m.toWeaklyDecreasing = strictSummand index m :=
-- proof
  rfl

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[starSummand_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
lemma starSummand_empty
  {m : WeaklyDecreasingTuple Index.empty.depth} :
-- imply
  starSummand Index.empty m = 1 := by
-- proof
  unfold starSummand
  have hempty : (Finset.univ : Finset (Fin Index.empty.depth)) = ∅ := by
    ext i
    exact Fin.elim0 (Index.empty_depth ▸ i)
  rw [hempty]
  simp only [Finset.prod_empty, inv_one]

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[starValue_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
lemma starValue_empty
-- given
  (h : Index.empty.IsAdmissibleOrEmpty) :
-- imply
  starValue Index.empty h = 1 := by
-- proof
  let m : WeaklyDecreasingTuple Index.empty.depth := by
    simpa only [Index.empty_depth] using WeaklyDecreasingTuple.empty
  unfold starValue
  rw [tsum_eq_single m]
  · exact starSummand_empty m
  · intro b hb
    exfalso
    apply hb
    apply Subtype.ext
    funext i
    exact Fin.elim0 (Index.empty_depth ▸ i)

end MetaMathlibExt.MultipleZeta

/--
[Index.empty_entries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
lemma Index.empty_entries
  :
-- imply
  Index.empty.entries = [] :=
-- proof
  rfl


namespace MetaMathlibExt.MultipleZeta

/--
[Index.empty_weight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
lemma Index.empty_weight
  :
-- imply
  Index.empty.weight = 0 :=
-- proof
  rfl

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[Index.entry_coe](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
lemma Index.entry_coe
  {index : Index}
  {i : Fin index.depth} :
-- imply
  (index.entry i : ℕ) = index.2.blocksFun i :=
-- proof
  rfl

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[StrictDecreasingTuple.eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
lemma StrictDecreasingTuple.eq_empty
  {m : StrictDecreasingTuple 0} :
-- imply
  m = StrictDecreasingTuple.empty := by
-- proof
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[WeaklyDecreasingTuple.eq_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Series.lean)
-/
@[path]
lemma WeaklyDecreasingTuple.eq_empty
  {m : WeaklyDecreasingTuple 0} :
-- imply
  m = WeaklyDecreasingTuple.empty := by
-- proof
  apply Subtype.ext
  funext i
  exact Fin.elim0 i

end MetaMathlibExt.MultipleZeta


-- created on 2026-10-20
-- updated on 2026-10-26
