import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MultipleZeta.WordAlgebra
open MetaMathlibExt.MultipleZeta


namespace MetaMathlibExt.MultipleZeta

/--
[mem_wordSubmonoidHOne_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
lemma mem_wordSubmonoidHOne_iff
  {w : FreeMonoid Bool} :
-- imply
  w ∈ wordSubmonoidHOne ↔ IsHOneWord w := by
-- proof
  rfl

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[mem_wordSubmonoidHZero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
lemma mem_wordSubmonoidHZero_iff
  {w : FreeMonoid Bool} :
-- imply
  w ∈ wordSubmonoidHZero ↔ IsHZeroWord w := by
-- proof
  rfl

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[wordSubmonoidHZero_le_wordSubmonoidHOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
lemma wordSubmonoidHZero_le_wordSubmonoidHOne
  :
-- imply
  wordSubmonoidHZero ≤ wordSubmonoidHOne := by
-- proof
  intro w hw
  change IsHZeroWord w at hw
  change IsHOneWord w
  obtain rfl | ⟨u, rfl⟩ := hw
  · exact Or.inl rfl
  · exact Or.inr ⟨xWord * u, by simp [mul_assoc]⟩

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[hZero_le_hOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
lemma hZero_le_hOne
  :
-- imply
  hZero ≤ hOne := by
-- proof
  intro x hx
  simp only [hZero, hOne, Subalgebra.mem_comap, AlgHom.mem_range] at hx ⊢
  obtain ⟨y, hy⟩ := hx
  have hle : wordSubmonoidHZero ≤ wordSubmonoidHOne :=
    wordSubmonoidHZero_le_wordSubmonoidHOne
  refine ⟨MonoidAlgebra.mapDomainAlgHom ℚ ℚ (Submonoid.inclusion hle) y, ?_⟩
  have hsubtype : wordSubmonoidHOne.subtype.comp (Submonoid.inclusion hle) =
    wordSubmonoidHZero.subtype :=
    Submonoid.subtype_comp_inclusion hle
  have hcomp : MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHZero.subtype =
    (MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHOne.subtype).comp
      (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (Submonoid.inclusion hle)) := by
    rw [← hsubtype, MonoidAlgebra.mapDomainAlgHom_comp]
  rw [hcomp] at hy
  change ((MonoidAlgebra.mapDomainAlgHom ℚ ℚ wordSubmonoidHOne.subtype).comp
    (MonoidAlgebra.mapDomainAlgHom ℚ ℚ (Submonoid.inclusion hle))) y =
      (FreeAlgebra.equivMonoidAlgebraFreeMonoid :
        FreeAlgebra ℚ Bool ≃ₐ[ℚ] MonoidAlgebra ℚ (FreeMonoid Bool)) x
  exact hy

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[zWord_mem_hOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
lemma zWord_mem_hOne
  {idx : Index} :
-- imply
  zWord idx ∈ wordSubmonoidHOne :=
-- proof
  zWordPNat_mem_hOne idx.pnatEntries

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[hoffmanBlock_mem_hZero_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
lemma hoffmanBlock_mem_hZero_of_two_le
  {k : PNat}
-- given
  (hk : 2 ≤ k.val) :
-- imply
  hoffmanBlock k ∈ wordSubmonoidHZero := by
-- proof
  obtain ⟨u, hu⟩ := exists_hoffmanBlock_eq_xWord_mul_yWord k hk
  change IsHZeroWord (hoffmanBlock k)
  exact Or.inr ⟨u, hu⟩

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[zMonomial_mem_hOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
lemma zMonomial_mem_hOne
  {idx : Index} :
-- imply
  zMonomial idx ∈ hOne := by
-- proof
  rw [mem_hOne_iff_support_subset]
  simpa [zMonomial] using zWord_mem_hOne idx

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[xWord_not_mem_hOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
lemma xWord_not_mem_hOne
  :
-- imply
  xWord ∉ wordSubmonoidHOne := by
-- proof
  change ¬IsHOneWord xWord
  intro h
  obtain h | ⟨u, hu⟩ := h
  · have hlist := congrArg FreeMonoid.toList h
    simp [xWord] at hlist
  · have hlist := congrArg FreeMonoid.toList hu
    have hlen := congrArg List.length hlist
    simp [xWord, yWord] at hlen
    simp [xWord, yWord, hlen] at hlist

end MetaMathlibExt.MultipleZeta

namespace MetaMathlibExt.MultipleZeta

/--
[generatorX_not_mem_hOne](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/WordAlgebra.lean)
-/
@[path]
lemma generatorX_not_mem_hOne
  :
-- imply
  FreeAlgebra.ι ℚ (false : Bool) ∉ hOne := by
-- proof
  rw [mem_hOne_iff_support_subset]
  intro h
  have hsupp :
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ)
      (FreeAlgebra.ι ℚ (false : Bool))).coeff.support = {xWord} := by
    have hx :
      FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ)
        (FreeAlgebra.ι ℚ (false : Bool)) = MonoidAlgebra.single xWord 1 := by
      simp [xWord, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
    rw [hx]
    simp
  have hxMem : xWord ∈
    (FreeAlgebra.equivMonoidAlgebraFreeMonoid (R := ℚ)
      (FreeAlgebra.ι ℚ (false : Bool))).coeff.support := by
    rw [hsupp]
    simp
  exact xWord_not_mem_hOne (h xWord hxMem)

end MetaMathlibExt.MultipleZeta

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


-- created on 2026-10-20
-- updated on 2026-10-23
