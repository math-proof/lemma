import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MultipleZeta.WordAlgebra
open MetaMathlibExt.MultipleZeta


/--
[mem_wordSubmonoidHOne_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma mem_wordSubmonoidHOne_iff_eq
  {w : FreeMonoid Bool} :
-- imply
  w ∈ wordSubmonoidHOne ↔ IsHOneWord w := by
-- proof
  apply MetaMathlibExt.MultipleZeta.mem_wordSubmonoidHOne_iff w

/--
[mem_wordSubmonoidHZero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma mem_wordSubmonoidHZero_iff_eq
  {w : FreeMonoid Bool} :
-- imply
  w ∈ wordSubmonoidHZero ↔ IsHZeroWord w := by
-- proof
  apply MetaMathlibExt.MultipleZeta.mem_wordSubmonoidHZero_iff w

/--
[wordSubmonoidHZero_le_wordSubmonoidHOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma wordSubmonoidHZero_le_wordSubmonoidHOne_eq
  :
-- imply
  wordSubmonoidHZero ≤ wordSubmonoidHOne := by
-- proof
  apply MetaMathlibExt.MultipleZeta.wordSubmonoidHZero_le_wordSubmonoidHOne

/--
[hZero_le_hOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma hZero_le_hOne_eq
  :
-- imply
  hZero ≤ hOne := by
-- proof
  apply MetaMathlibExt.MultipleZeta.hZero_le_hOne

/--
[pnatEntries_val](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma pnatEntries_val_eq
  {idx : Index} :
-- imply
  idx.pnatEntries.map PNat.val = idx.entries := by
-- proof
  apply MetaMathlibExt.MultipleZeta.pnatEntries_val idx

/--
[zWord_eq_one_of_entries_eq_nil](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma zWord_eq_one_of_entries_eq_nil_eq
  {idx : Index}
-- given
  (h : idx.entries = []) :
-- imply
  zWord idx = 1 := by
-- proof
  apply MetaMathlibExt.MultipleZeta.zWord_eq_one_of_entries_eq_nil idx h

/--
[zWordPNat_mem_hOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma zWordPNat_mem_hOne_eq
  {l : List PNat} :
-- imply
  zWordPNat l ∈ wordSubmonoidHOne := by
-- proof
  apply MetaMathlibExt.MultipleZeta.zWordPNat_mem_hOne l

/--
[zWord_mem_hOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma zWord_mem_hOne_eq
  {idx : Index} :
-- imply
  zWord idx ∈ wordSubmonoidHOne := by
-- proof
  apply MetaMathlibExt.MultipleZeta.zWord_mem_hOne idx

/--
[exists_hoffmanBlock_eq_xWord_mul_yWord](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma exists_hoffmanBlock_eq_xWord_mul_yWord_eq
  {k : PNat}
-- given
  (hk : 2 ≤ k.val) :
-- imply
  ∃ u, hoffmanBlock k = xWord * u * yWord := by
-- proof
  apply MetaMathlibExt.MultipleZeta.exists_hoffmanBlock_eq_xWord_mul_yWord k hk

/--
[hoffmanBlock_mem_hZero_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma hoffmanBlock_mem_hZero_of_two_le_eq
  {k : PNat}
-- given
  (hk : 2 ≤ k.val) :
-- imply
  hoffmanBlock k ∈ wordSubmonoidHZero := by
-- proof
  apply MetaMathlibExt.MultipleZeta.hoffmanBlock_mem_hZero_of_two_le k hk

/--
[zWord_mem_hZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma zWord_mem_hZero_eq
  {idx : Index}
-- given
  (h : IsHZeroIndex idx) :
-- imply
  zWord idx ∈ wordSubmonoidHZero := by
-- proof
  apply MetaMathlibExt.MultipleZeta.zWord_mem_hZero idx h

/--
[mem_hOne_iff_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma mem_hOne_iff_support_subset_eq
  {a : FreeAlgebra ℚ Bool} :
-- imply
  a ∈ hOne ↔
    ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := by
-- proof
  apply MetaMathlibExt.MultipleZeta.mem_hOne_iff_support_subset a

/--
[mem_hZero_iff_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma mem_hZero_iff_support_subset_eq
  {a : FreeAlgebra ℚ Bool} :
-- imply
  a ∈ hZero ↔
    ∀ w ∈ (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := by
-- proof
  apply MetaMathlibExt.MultipleZeta.mem_hZero_iff_support_subset a

/--
[zMonomial_mem_hOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma zMonomial_mem_hOne_eq
  {idx : Index} :
-- imply
  zMonomial idx ∈ hOne := by
-- proof
  apply MetaMathlibExt.MultipleZeta.zMonomial_mem_hOne idx

/--
[zMonomial_mem_hZero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma zMonomial_mem_hZero_eq
  {idx : Index}
-- given
  (h : IsHZeroIndex idx) :
-- imply
  zMonomial idx ∈ hZero := by
-- proof
  apply MetaMathlibExt.MultipleZeta.zMonomial_mem_hZero idx h

/--
[xWord_not_mem_hOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma xWord_not_mem_hOne_eq
  :
-- imply
  xWord ∉ wordSubmonoidHOne := by
-- proof
  apply MetaMathlibExt.MultipleZeta.xWord_not_mem_hOne

/--
[generatorX_not_mem_hOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
private lemma generatorX_not_mem_hOne_eq
  :
-- imply
  FreeAlgebra.ι ℚ (false : Bool) ∉ hOne := by
-- proof
  apply MetaMathlibExt.MultipleZeta.generatorX_not_mem_hOne


-- created on 2026-10-20
