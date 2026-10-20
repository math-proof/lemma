import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.ExtensionDiscriminantLocalization


/--
[extensionDiscriminant_localization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean)
-/
@[path]
private lemma extensionDiscriminant_localization_eq
  [CommRing A] [Field K] [CommRing B] [Algebra A K] [Algebra A B] [CommRing SA] [Algebra A SA] [CommRing SB] [Algebra B SB] [Algebra SA K] [Algebra SA SB] [IsScalarTower A SA K]
  {L : Type u} [Field L] [Algebra B L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L] [Algebra SB L] [Algebra SA L] [IsScalarTower SA K L] [IsScalarTower SA SB L] [IsScalarTower B SB L]
  {S : Submonoid A} [IsLocalization S SA] [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] :
-- imply
  Submodule.span SA (extensionDiscriminant A K L B : Set K) =
    extensionDiscriminant SA K L SB := by
-- proof
  apply extensionDiscriminant_localization A K L B S SA SB


-- created on 2026-10-20
