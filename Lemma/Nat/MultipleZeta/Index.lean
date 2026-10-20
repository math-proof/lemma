import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MultipleZeta.Index
open MetaMathlibExt.MultipleZeta


/--
[isAdmissible_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Index.lean)
-/
@[path]
private lemma isAdmissible_nil_eq
  :
-- imply
  ¬IsAdmissible [] := by
-- proof
  apply MetaMathlibExt.MultipleZeta.isAdmissible_nil

/--
[isAdmissible_cons_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/Index.lean)
-/
@[path]
private lemma isAdmissible_cons_iff_eq
  {t : List ℕ}
-- given
  (h : ℕ) :
-- imply
  IsAdmissible (h :: t) ↔ 2 ≤ h ∧ ∀ x ∈ t, 0 < x := by
-- proof
  apply MetaMathlibExt.MultipleZeta.isAdmissible_cons_iff h t

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
