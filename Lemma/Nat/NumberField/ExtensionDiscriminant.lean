import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.NumberField.ExtensionDiscriminant.Part2


/--
[algebraMap_mem_imageOfB](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminant.lean)
-/
@[path]
lemma algebraMap_mem_imageOfB
  [CommRing A] [CommRing B] [Algebra A B]
  {L : Type u} [Field L] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
  {b : B} :
-- imply
  algebraMap B L b ∈ imageOfB A L B :=
-- proof
  (mem_imageOfB A L B).mpr ⟨b, rfl⟩

/--
[extensionDiscriminant_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminant.lean)
-/
@[path]
lemma extensionDiscriminant_eq
  [CommRing A] [Field K] [CommRing B] [Algebra A K] [Algebra A B]
  {L : Type u} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L] :
-- imply
  extensionDiscriminant A K L B =
    latticeDiscriminant A K (imageOfB A L B) :=
-- proof
  rfl

/--
[discr_mem_extensionDiscriminant](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminant.lean)
-/
@[path]
lemma discr_mem_extensionDiscriminant
  [CommRing A] [Field K] [CommRing B] [Algebra A K] [Algebra A B]
  {L : Type u} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L]
  {b : Fin (Module.finrank K L) → L}
-- given
  (hb : ∀ i, b i ∈ imageOfB A L B) :
-- imply
  Algebra.discr K b ∈ extensionDiscriminant A K L B :=
-- proof
  discr_mem_latticeDiscriminant A K hb

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


-- created on 2026-10-20
-- updated on 2026-10-26
