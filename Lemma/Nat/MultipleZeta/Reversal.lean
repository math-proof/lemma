import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.MultipleZeta.Reversal.Part2
open MetaMathlibExt.MultipleZeta


namespace MetaMathlibExt.MultipleZeta

/--
[composition_blocksFun_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
private lemma composition_blocksFun_reverse {n : ℕ}
  (composition : Composition n)
  (i : Fin composition.reverse.blocks.length) :
  Composition.blocksFun composition.reverse i =
    Composition.blocksFun composition
      (Fin.rev (Fin.castOrderIso (by simp) i)) := by
  simp only [Composition.blocksFun, Composition.reverse_blocks,
    List.get_eq_getElem, List.getElem_reverse, Fin.val_rev, Nat.sub_sub]
  apply getElem_congr rfl
  change composition.blocks.length - (1 + i.val) =
    composition.blocks.length - (i.val + 1)
  omega

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[Index.reverse_entry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
lemma Index.reverse_entry
  {index : Index}
  {i : Fin index.reverse.depth} :
-- imply
  index.reverse.entry i =
    index.entry (Fin.rev (Fin.castOrderIso index.reverse_depth i)) := by
-- proof
  obtain ⟨n, composition⟩ := index
  apply PNat.eq
  exact composition_blocksFun_reverse composition i

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[increasingSummand_eq_strictSummand_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
lemma increasingSummand_eq_strictSummand_reverse
  {index : Index}
  {m : StrictIncreasingTuple index.depth} :
-- imply
  increasingSummand index m =
    strictSummand index.reverse (increasingEquivDecreasing index m) := by
-- proof
  unfold increasingSummand strictSummand
  let e : Fin index.reverse.depth ≃ Fin index.depth :=
    (Fin.castOrderIso index.reverse_depth).toEquiv.trans Fin.revPerm
  have hprod :
    (∏ i : Fin index.depth, ((m.1 i : ℝ) ^ (index.entry i : ℕ))) =
      ∏ j : Fin index.reverse.depth,
        ((m.1 (e j) : ℝ) ^ (index.reverse.entry j : ℕ)) := by
    symm
    apply Fintype.prod_equiv e
    intro j
    simp [e, Index.reverse_entry]
  rw [hprod]
  rfl

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[increasingValue_eq_strictValue_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
lemma increasingValue_eq_strictValue_reverse
  {index : Index}
-- given
  (h : index.IsIncreasingAdmissible) :
-- imply
  increasingValue index h =
    strictValue index.reverse
    (Or.inl (index.isIncreasingAdmissible_iff_reverse_isAdmissible.mp h)) := by
-- proof
  unfold increasingValue strictValue
  rw [show (fun m : StrictIncreasingTuple index.depth =>
    increasingSummand index m) =
    fun m => strictSummand index.reverse
      (increasingEquivDecreasing index m) by
    funext m
    exact increasingSummand_eq_strictSummand_reverse index m]
  exact Equiv.tsum_eq (increasingEquivDecreasing index)
    (strictSummand index.reverse)

end MetaMathlibExt.MultipleZeta

/--
[Index.reverse_entries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
lemma Index.reverse_entries
  {index : Index} :
-- imply
  index.reverse.entries = index.entries.reverse := by
-- proof
  obtain ⟨n, composition⟩ := index
  simp [Index.entries, Index.reverse, Composition.reverse_blocks]


namespace MetaMathlibExt.MultipleZeta

/--
[Index.reverse_weight](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
lemma Index.reverse_weight
  {index : Index} :
-- imply
  index.reverse.weight = index.weight := by
-- proof
  obtain ⟨n, composition⟩ := index
  rfl

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[Index.reverse_depth](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
lemma Index.reverse_depth
  {index : Index} :
-- imply
  index.reverse.depth = index.depth := by
-- proof
  obtain ⟨n, composition⟩ := index
  change composition.reverse.blocks.length = composition.blocks.length
  simp

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[Index.reverse_reverse](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
lemma Index.reverse_reverse
  {index : Index} :
-- imply
  index.reverse.reverse = index := by
-- proof
  obtain ⟨n, composition⟩ := index
  simp only [Index.reverse]
  rw [Composition.reverse_reverse]

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[Index.isIncreasingAdmissible_iff_reverse_isAdmissible](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
lemma Index.isIncreasingAdmissible_iff_reverse_isAdmissible
  {index : Index} :
-- imply
  index.IsIncreasingAdmissible ↔ index.reverse.IsAdmissible := by
-- proof
  rw [Index.isAdmissible_iff, Index.reverse_entries]
  rfl

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[increasingEquivDecreasing_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Reversal.lean)
-/
@[path]
lemma increasingEquivDecreasing_apply
  {index : Index}
  {m : StrictIncreasingTuple index.depth}
  {i : Fin index.reverse.depth} :
-- imply
  (increasingEquivDecreasing index m).1 i =
    m.1 (Fin.rev (Fin.castOrderIso index.reverse_depth i)) :=
-- proof
  rfl

end MetaMathlibExt.MultipleZeta


-- created on 2026-10-20
-- updated on 2026-10-26
