import Mathlib
import Abbrev.NumberField_Extension
import Instance.NumberField_Extension
import Class.NumberField_Extension
import Def.NumberField_Extension

section

noncomputable section

namespace NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
  (f : K →+* ℂ) (g : L →+* ℂ)

theorem IsExtension.not_isExtension_conjugate (h : IsExtension f g)
    (hf : ¬ComplexEmbedding.IsReal f) :
    ¬IsExtension f (conjugate g) := by
  simp_all [RingHom.ext_iff, ComplexEmbedding.isReal_iff]

variable {f g} in
theorem IsExtension.ne {r : L →+* ℂ} (hg : IsExtension f g) (hr : ¬IsExtension f r) :
    g ≠ r := by
  simp_all only [← hg, RingHom.ext_iff, RingHom.coe_comp, Function.comp_apply, not_forall,
    ne_eq]
  let ⟨x, hx⟩ := hr
  exact ⟨algebraMap K L x, by aesop⟩

theorem not_isReal_of_not_isReal {f : K →+* ℂ} {g : L →+* ℂ} (h : IsExtension f g)
    (hf : ¬ComplexEmbedding.IsReal f) :
    ¬ComplexEmbedding.IsReal g :=
  mt (IsReal.comp _) (h ▸ hf)

namespace IsMixedExtension

theorem isExtension (h : IsMixedExtension f g) :
    IsExtension f g := h.1

theorem isReal (h : IsMixedExtension f g) :
    ComplexEmbedding.IsReal f := h.2.1

theorem not_isReal (h : IsMixedExtension f g) :
    ¬ComplexEmbedding.IsReal g := h.2.2

end IsMixedExtension

theorem IsUnmixedExtension.isReal_of_isReal (h : IsUnmixedExtension f g)
    (hf : ComplexEmbedding.IsReal f) :
    ComplexEmbedding.IsReal g := by
  simp only [IsUnmixedExtension, not_and, not_not] at h
  exact h.2 h.1 hf

end NumberField.ComplexEmbedding

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding

variable {K : Type*} {L : Type*} [Field K] [Field L] (v : InfinitePlace K) (w : InfinitePlace L)

variable [Algebra K L]

variable (L) in

theorem coe_toExtension (w : InfinitePlace L) : (toExtension K w).1 = w := rfl

namespace Extension

variable {v : InfinitePlace K} (w : v.Extension L)

theorem isComplex_of_isComplex (hv : v.IsComplex) :
    w.1.IsComplex := by
  rw [isComplex_iff, ComplexEmbedding.isReal_iff, RingHom.ext_iff, not_forall] at hv ⊢
  let ⟨x, hx⟩ := hv
  use algebraMap K L x
  rw [← w.2, ← mk_embedding w.1, comap_mk] at hx
  cases embedding_mk_eq (w.1.embedding.comp (algebraMap K L)) with
  | inl hl => simp_all
  | inr hr => aesop

theorem isReal_base (hw : w.1.IsReal) :
    v.IsReal := by
  simp_all only [← not_isComplex_iff_isReal]
  exact mt w.isComplex_of_isComplex hw

theorem mk_embedding : mk (w.1.embedding.comp (algebraMap K L)) = v := by
  rw [← comap_mk, w.1.mk_embedding, w.2]

theorem isExtension_or_isExtension_conjugate :
    IsExtension v.embedding w.1.embedding ∨ IsExtension v.embedding (conjugate w.1.embedding) := by
  cases embedding_mk_eq (w.1.embedding.comp (algebraMap K L)) with
  | inl hl =>
    convert Or.inl <| hl ▸ congrArg InfinitePlace.embedding w.mk_embedding
  | inr hr =>
    convert Or.inr <| hr ▸ congrArg InfinitePlace.embedding w.mk_embedding
    rfl

theorem isExtension_conjugate_of_not_isExtension (h : ¬IsExtension v.embedding w.1.embedding) :
    IsExtension v.embedding (conjugate w.1.embedding) :=
  w.isExtension_or_isExtension_conjugate.resolve_left h

variable (L)

variable (v : InfinitePlace K) (w : v.Extension L)

theorem IsLift.isExtension [w.IsLift L v] : IsExtension v.embedding w.1.embedding :=
  IsLift.isExtension'

theorem IsConjugateLift.isExtension [w.IsConjugateLift L v] :
    IsExtension v.embedding (conjugate w.1.embedding) := IsConjugateLift.isExtension'

theorem isLift_or_isConjugateLift (v : InfinitePlace K) (w : v.Extension L) :
    w.IsLift L v ∨ w.IsConjugateLift L v := by
  cases isExtension_or_isExtension_conjugate w with
  | inl hl => exact Or.inl ⟨hl⟩
  | inr hr => exact Or.inr ⟨hr⟩

end Extension

variable (L)


namespace RamifiedExtension

theorem comap_eq (w : v.RamifiedExtension L) : w.1.comap (algebraMap K L) = v := w.2.1

theorem isRamified (w : v.RamifiedExtension L) : w.1.IsRamified K := w.2.2

theorem isReal_comap (w : v.RamifiedExtension L) : (w.1.comap (algebraMap K L)).IsReal :=
  (isRamified_iff.1 w.isRamified).2

theorem isReal (w : v.RamifiedExtension L) : v.IsReal :=
  w.comap_eq ▸ w.isReal_comap

theorem isComplex (w : v.RamifiedExtension L) :
    (w.1 : InfinitePlace L).IsComplex :=
  (isRamified_iff.1 w.isRamified).1

end RamifiedExtension

namespace UnramifiedExtension

theorem comap_eq (w : UnramifiedExtension L v) : w.1.comap (algebraMap K L) = v := w.2.1

theorem isUnramified (w : UnramifiedExtension L v) : w.1.IsUnramified K := w.2.2

end UnramifiedExtension

end NumberField.InfinitePlace

end

end
