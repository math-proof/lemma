import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.ExtensionDiscriminant


/--
[mem_imageOfB](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminant.lean)
-/
@[path]
private lemma mem_imageOfB_eq
  [CommRing A] [CommRing B] [Algebra A B]
  {L : Type u} [Field L] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
  {x : L} :
-- imply
  x ∈ imageOfB A L B ↔ ∃ b : B, algebraMap B L b = x := by
-- proof
  apply mem_imageOfB A L B

/--
[algebraMap_mem_imageOfB](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminant.lean)
-/
@[path]
private lemma algebraMap_mem_imageOfB_eq
  [CommRing A] [CommRing B] [Algebra A B]
  {L : Type u} [Field L] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
  {b : B} :
-- imply
  algebraMap B L b ∈ imageOfB A L B := by
-- proof
  apply algebraMap_mem_imageOfB A L B b

/--
[extensionDiscriminant_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminant.lean)
-/
@[path]
private lemma extensionDiscriminant_eq_eq
  [CommRing A] [Field K] [CommRing B] [Algebra A K] [Algebra A B]
  {L : Type u} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L] :
-- imply
  extensionDiscriminant A K L B =
    latticeDiscriminant A K (imageOfB A L B) := by
-- proof
  apply extensionDiscriminant_eq A K L B

/--
[discr_mem_extensionDiscriminant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminant.lean)
-/
@[path]
private lemma discr_mem_extensionDiscriminant_eq
  [CommRing A] [Field K] [CommRing B] [Algebra A K] [Algebra A B]
  {L : Type u} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L]
  {b : Fin (Module.finrank K L) → L}
-- given
  (hb : ∀ i, b i ∈ imageOfB A L B) :
-- imply
  Algebra.discr K b ∈ extensionDiscriminant A K L B := by
-- proof
  apply discr_mem_extensionDiscriminant A K L B hb


-- created on 2026-10-20
