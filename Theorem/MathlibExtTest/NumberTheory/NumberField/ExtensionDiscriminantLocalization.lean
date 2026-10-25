/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminantLocalization.lean -/


import Lemma.Nat.NumberField.ExtensionDiscriminantLocalization


-- Generic restatement applying `extensionDiscriminant_localization`.
example (A K : Type*) (L : Type*) (B : Type*) [CommRing A] [Field K]
    [CommRing B] [Field L] [Algebra A K] [Algebra B L] [Algebra A B]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
    [FiniteDimensional K L] (S : Submonoid A)
    (SA : Type*) [CommRing SA] [Algebra A SA] [IsLocalization S SA]
    (SB : Type*) [CommRing SB] [Algebra B SB]
    [IsLocalization (Algebra.algebraMapSubmonoid B S) SB] [Algebra SA K]
    [Algebra SB L] [Algebra SA SB] [Algebra SA L] [IsScalarTower SA K L]
    [IsScalarTower SA SB L] [IsScalarTower A SA K] [IsScalarTower B SB L] :
    Submodule.span SA (extensionDiscriminant A K L B : Set K) =
      extensionDiscriminant SA K L SB :=
  extensionDiscriminant_localization A K L B S SA SB

