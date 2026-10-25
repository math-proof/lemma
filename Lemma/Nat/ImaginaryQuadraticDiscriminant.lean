import Mathlib
import sympy.Basic
import Def.NumberTheory.ImaginaryQuadraticDiscriminant.Part2
open ImaginaryQuadraticDiscriminant
open ImaginaryQuadraticDiscriminantDecomposition


namespace ImaginaryQuadraticDiscriminant

/--
[isImaginaryQuadraticDiscriminant_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma isImaginaryQuadraticDiscriminant_iff
  {D : Int} :
-- imply
  IsImaginaryQuadraticDiscriminant D ↔ D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1) :=
-- proof
  Iff.rfl

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant

/--
[isFundamentalImaginaryQuadraticDiscriminant_isFundamentalDiscriminant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma isFundamentalImaginaryQuadraticDiscriminant_isFundamentalDiscriminant
  {D : Int}
-- given
  (h : IsFundamentalImaginaryQuadraticDiscriminant D) :
-- imply
  MetaMathlibExt.IsFundamentalDiscriminant D :=
-- proof
  h.2

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant

/--
[isFundamentalImaginaryQuadraticDiscriminant_isImaginary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma isFundamentalImaginaryQuadraticDiscriminant_isImaginary
  {D : Int}
-- given
  (h : IsFundamentalImaginaryQuadraticDiscriminant D) :
-- imply
  IsImaginaryQuadraticDiscriminant D := by
-- proof
  obtain ⟨hneg, hfund⟩ := h
  unfold MetaMathlibExt.IsFundamentalDiscriminant at hfund
  obtain ⟨_, hmod1⟩ | ⟨m, hDm, _, _⟩ := hfund
  · exact ⟨hneg, Or.inr hmod1⟩
  · have h0 : D % 4 = 0 := by simp [hDm]
    exact ⟨hneg, Or.inl h0⟩
namespace ImaginaryQuadraticDiscriminantDecomposition
variable {D : Int}

end ImaginaryQuadraticDiscriminant

/--
[mem_imaginaryQuadraticDiscriminants](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma mem_imaginaryQuadraticDiscriminants
  {D : Int} :
-- imply
  D ∈ imaginaryQuadraticDiscriminants ↔ IsImaginaryQuadraticDiscriminant D :=
-- proof
  Iff.rfl


namespace ImaginaryQuadraticDiscriminant

/--
[mem_fundamentalImaginaryQuadraticDiscriminants](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma mem_fundamentalImaginaryQuadraticDiscriminants
  {D : Int} :
-- imply
  D ∈ fundamentalImaginaryQuadraticDiscriminants ↔
    IsFundamentalImaginaryQuadraticDiscriminant D :=
-- proof
  Iff.rfl

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant

/--
[isImaginaryQuadraticDiscriminant_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma isImaginaryQuadraticDiscriminant_mk
  {D : Int}
-- given
  (hneg : D < 0)
  (hmod : D % 4 = 0 ∨ D % 4 = 1) :
-- imply
  IsImaginaryQuadraticDiscriminant D :=
-- proof
  ⟨hneg, hmod⟩

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant

/--
[isImaginaryQuadraticDiscriminant_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma isImaginaryQuadraticDiscriminant_neg
  {D : Int}
-- given
  (h : IsImaginaryQuadraticDiscriminant D) :
-- imply
  D < 0 :=
-- proof
  h.1

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant

/--
[isImaginaryQuadraticDiscriminant_mod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma isImaginaryQuadraticDiscriminant_mod
  {D : Int}
-- given
  (h : IsImaginaryQuadraticDiscriminant D) :
-- imply
  D % 4 = 0 ∨ D % 4 = 1 :=
-- proof
  h.2

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant

/--
[isImaginaryQuadraticDiscriminant_of_mod_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma isImaginaryQuadraticDiscriminant_of_mod_zero
  {D : Int}
-- given
  (hneg : D < 0)
  (hmod : D % 4 = 0) :
-- imply
  IsImaginaryQuadraticDiscriminant D :=
-- proof
  ⟨hneg, Or.inl hmod⟩

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant

/--
[isImaginaryQuadraticDiscriminant_of_mod_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma isImaginaryQuadraticDiscriminant_of_mod_one
  {D : Int}
-- given
  (hneg : D < 0)
  (hmod : D % 4 = 1) :
-- imply
  IsImaginaryQuadraticDiscriminant D :=
-- proof
  ⟨hneg, Or.inr hmod⟩

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant

/--
[isFundamentalImaginaryQuadraticDiscriminant_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma isFundamentalImaginaryQuadraticDiscriminant_iff
  {D : Int} :
-- imply
  IsFundamentalImaginaryQuadraticDiscriminant D ↔
    D < 0 ∧ MetaMathlibExt.IsFundamentalDiscriminant D :=
-- proof
  Iff.rfl

end ImaginaryQuadraticDiscriminant

namespace ImaginaryQuadraticDiscriminant.ImaginaryQuadraticDiscriminantDecomposition

/--
[isFundamental](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma isFundamental
  {D : Int}
-- given
  (h : ImaginaryQuadraticDiscriminantDecomposition D) :
-- imply
  IsFundamentalImaginaryQuadraticDiscriminant h.D_K :=
-- proof
  h.hD_K

end ImaginaryQuadraticDiscriminant.ImaginaryQuadraticDiscriminantDecomposition

namespace ImaginaryQuadraticDiscriminant.ImaginaryQuadraticDiscriminantDecomposition

/--
[u_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma u_ge_one
  {D : Int}
-- given
  (h : ImaginaryQuadraticDiscriminantDecomposition D) :
-- imply
  h.u ≥ 1 :=
-- proof
  h.hu

end ImaginaryQuadraticDiscriminant.ImaginaryQuadraticDiscriminantDecomposition

namespace ImaginaryQuadraticDiscriminant.ImaginaryQuadraticDiscriminantDecomposition

/--
[prop_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
lemma prop_eq
  {D : Int}
-- given
  (h : ImaginaryQuadraticDiscriminantDecomposition D) :
-- imply
  D = h.u ^ 2 * h.D_K :=
-- proof
  h.hD

end ImaginaryQuadraticDiscriminant.ImaginaryQuadraticDiscriminantDecomposition

/--
[isFundamentalImaginaryQuadraticDiscriminant_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma isFundamentalImaginaryQuadraticDiscriminant_mk_eq
  {D : Int}
-- given
  (hneg : D < 0)
  (hfund : MetaMathlibExt.IsFundamentalDiscriminant D) :
-- imply
  IsFundamentalImaginaryQuadraticDiscriminant D := by
-- proof
  apply ImaginaryQuadraticDiscriminant.isFundamentalImaginaryQuadraticDiscriminant_mk hneg hfund


-- created on 2026-10-20
-- updated on 2026-10-23
