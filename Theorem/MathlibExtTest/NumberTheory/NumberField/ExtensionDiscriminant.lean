/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/ExtensionDiscriminant.lean -/


import Def.NumberTheory.NumberField.ExtensionDiscriminant.Part2
import Lemma.Nat.NumberField.ExtensionDiscriminant
set_option autoImplicit false

universe u


section ImageOfB

variable (A : Type*) (L : Type u) (B : Type*)
  [CommRing A] [CommRing B] [Field L]
  [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]

example (b : B) : algebraMap B L b ∈ imageOfB A L B :=
  algebraMap_mem_imageOfB A L B b

end ImageOfB

section ExtensionDiscriminant

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L]

example (b : Fin (Module.finrank K L) → B) :
    Algebra.discr K (fun i => algebraMap B L (b i)) ∈
      extensionDiscriminant A K L B := by
  apply discr_mem_extensionDiscriminant A K L B
  intro i
  exact algebraMap_mem_imageOfB A L B (b i)

example :
    extensionDiscriminant A K L B =
      latticeDiscriminant A K (imageOfB A L B) :=
  extensionDiscriminant_eq A K L B

end ExtensionDiscriminant

example : imageOfB ℚ ℚ ℚ = ⊤ := by
  ext x
  constructor
  · intro _
    exact Submodule.mem_top
  · intro _
    exact (mem_imageOfB ℚ ℚ ℚ).mpr ⟨x, by simp⟩

