import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.ImaginaryQuadraticDiscriminant
open ImaginaryQuadraticDiscriminant
open ImaginaryQuadraticDiscriminantDecomposition


/--
[mem_imaginaryQuadraticDiscriminants](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma mem_imaginaryQuadraticDiscriminants_eq
  {D : Int} :
-- imply
  D ∈ imaginaryQuadraticDiscriminants ↔ IsImaginaryQuadraticDiscriminant D := by
-- proof
  apply ImaginaryQuadraticDiscriminant.mem_imaginaryQuadraticDiscriminants

/--
[mem_fundamentalImaginaryQuadraticDiscriminants](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma mem_fundamentalImaginaryQuadraticDiscriminants_eq
  {D : Int} :
-- imply
  D ∈ fundamentalImaginaryQuadraticDiscriminants ↔
    IsFundamentalImaginaryQuadraticDiscriminant D := by
-- proof
  apply ImaginaryQuadraticDiscriminant.mem_fundamentalImaginaryQuadraticDiscriminants

/--
[isImaginaryQuadraticDiscriminant_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma isImaginaryQuadraticDiscriminant_iff_eq
  {D : Int} :
-- imply
  IsImaginaryQuadraticDiscriminant D ↔ D < 0 ∧ (D % 4 = 0 ∨ D % 4 = 1) := by
-- proof
  apply ImaginaryQuadraticDiscriminant.isImaginaryQuadraticDiscriminant_iff D

/--
[isImaginaryQuadraticDiscriminant_mk](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma isImaginaryQuadraticDiscriminant_mk_eq
  {D : Int}
-- given
  (hneg : D < 0)
  (hmod : D % 4 = 0 ∨ D % 4 = 1) :
-- imply
  IsImaginaryQuadraticDiscriminant D := by
-- proof
  apply ImaginaryQuadraticDiscriminant.isImaginaryQuadraticDiscriminant_mk hneg hmod

/--
[isImaginaryQuadraticDiscriminant_neg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma isImaginaryQuadraticDiscriminant_neg_eq
  {D : Int}
-- given
  (h : IsImaginaryQuadraticDiscriminant D) :
-- imply
  D < 0 := by
-- proof
  apply ImaginaryQuadraticDiscriminant.isImaginaryQuadraticDiscriminant_neg h

/--
[isImaginaryQuadraticDiscriminant_mod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma isImaginaryQuadraticDiscriminant_mod_eq
  {D : Int}
-- given
  (h : IsImaginaryQuadraticDiscriminant D) :
-- imply
  D % 4 = 0 ∨ D % 4 = 1 := by
-- proof
  apply ImaginaryQuadraticDiscriminant.isImaginaryQuadraticDiscriminant_mod h

/--
[isImaginaryQuadraticDiscriminant_of_mod_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma isImaginaryQuadraticDiscriminant_of_mod_zero_eq
  {D : Int}
-- given
  (hneg : D < 0)
  (hmod : D % 4 = 0) :
-- imply
  IsImaginaryQuadraticDiscriminant D := by
-- proof
  apply ImaginaryQuadraticDiscriminant.isImaginaryQuadraticDiscriminant_of_mod_zero hneg hmod

/--
[isImaginaryQuadraticDiscriminant_of_mod_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma isImaginaryQuadraticDiscriminant_of_mod_one_eq
  {D : Int}
-- given
  (hneg : D < 0)
  (hmod : D % 4 = 1) :
-- imply
  IsImaginaryQuadraticDiscriminant D := by
-- proof
  apply ImaginaryQuadraticDiscriminant.isImaginaryQuadraticDiscriminant_of_mod_one hneg hmod

/--
[isFundamentalImaginaryQuadraticDiscriminant_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma isFundamentalImaginaryQuadraticDiscriminant_iff_eq
  {D : Int} :
-- imply
  IsFundamentalImaginaryQuadraticDiscriminant D ↔
    D < 0 ∧ MetaMathlibExt.IsFundamentalDiscriminant D := by
-- proof
  apply ImaginaryQuadraticDiscriminant.isFundamentalImaginaryQuadraticDiscriminant_iff D

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

/--
[isFundamentalImaginaryQuadraticDiscriminant_isFundamentalDiscriminant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma isFundamentalImaginaryQuadraticDiscriminant_isFundamentalDiscriminant_eq
  {D : Int}
-- given
  (h : IsFundamentalImaginaryQuadraticDiscriminant D) :
-- imply
  MetaMathlibExt.IsFundamentalDiscriminant D := by
-- proof
  apply ImaginaryQuadraticDiscriminant.isFundamentalImaginaryQuadraticDiscriminant_isFundamentalDiscriminant h

/--
[isFundamentalImaginaryQuadraticDiscriminant_isImaginary](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma isFundamentalImaginaryQuadraticDiscriminant_isImaginary_eq
  {D : Int}
-- given
  (h : IsFundamentalImaginaryQuadraticDiscriminant D) :
-- imply
  IsImaginaryQuadraticDiscriminant D := by
-- proof
  apply ImaginaryQuadraticDiscriminant.isFundamentalImaginaryQuadraticDiscriminant_isImaginary h

/--
[isFundamental](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma isFundamental_eq
  {D : Int}
-- given
  (h : ImaginaryQuadraticDiscriminantDecomposition D) :
-- imply
  IsFundamentalImaginaryQuadraticDiscriminant h.D_K := by
-- proof
  apply ImaginaryQuadraticDiscriminant.ImaginaryQuadraticDiscriminantDecomposition.isFundamental h

/--
[u_ge_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma u_ge_one_eq
  {D : Int}
-- given
  (h : ImaginaryQuadraticDiscriminantDecomposition D) :
-- imply
  h.u ≥ 1 := by
-- proof
  apply ImaginaryQuadraticDiscriminant.ImaginaryQuadraticDiscriminantDecomposition.u_ge_one h

/--
[prop_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ImaginaryQuadraticDiscriminant.lean)
-/
@[path]
private lemma prop_eq_eq
  {D : Int}
-- given
  (h : ImaginaryQuadraticDiscriminantDecomposition D) :
-- imply
  D = h.u ^ 2 * h.D_K := by
-- proof
  apply ImaginaryQuadraticDiscriminant.ImaginaryQuadraticDiscriminantDecomposition.prop_eq h


-- created on 2026-10-20
