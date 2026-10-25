import Mathlib
import sympy.Basic
import Theorem.NumberTheory.MultipleZeta.Index.Part2
open MetaMathlibExt.MultipleZeta


namespace MetaMathlibExt.MultipleZeta

/--
[isAdmissible_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Index.lean)
-/
@[path]
lemma isAdmissible_nil
  :
-- imply
  ¬IsAdmissible [] := by
-- proof
  simp [IsAdmissible]

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[isAdmissible_cons_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Index.lean)
-/
@[path]
lemma isAdmissible_cons_iff
  {t : List ℕ}
-- given
  (h : ℕ) :
-- imply
  IsAdmissible (h :: t) ↔ 2 ≤ h ∧ ∀ x ∈ t, 0 < x := by
-- proof
  rfl

end MetaMathlibExt.MultipleZeta

/--
[Index.isAdmissible_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Index.lean)
-/
@[path]
private lemma Index_isAdmissible_iff_eq
  {index : Index} :
-- imply
  index.IsAdmissible ↔ IsAdmissible index.entries := by
-- proof
  apply MetaMathlibExt.MultipleZeta.Index.isAdmissible_iff index

/--
[toList_hoffmanBlock](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Index.lean)
-/
@[path]
private lemma toList_hoffmanBlock_eq
  {k : PNat} :
-- imply
  FreeMonoid.toList (hoffmanBlock k) =
      List.replicate (k.val - 1) false ++ [true] := by
-- proof
  apply MetaMathlibExt.MultipleZeta.toList_hoffmanBlock k


-- created on 2026-10-20
-- updated on 2026-10-23
