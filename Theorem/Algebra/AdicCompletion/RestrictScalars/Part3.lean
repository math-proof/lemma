import Mathlib.RingTheory.AdicCompletion.Algebra
import Def.Algebra.AdicCompletion.RestrictScalars.Part2
universe u₁ u₂


namespace AdicCompletion

variable {A : Type u₁} [CommRing A] (B : Type u₂) [CommRing B] [Algebra A B] (𝔭 : Ideal A)

theorem restrictScalarsEquiv_of (b : B) :
    restrictScalarsEquiv B 𝔭 (of (𝔭.map (algebraMap A B)) B b) = of 𝔭 B b := by
  ext n
  rfl

theorem restrictScalarsEquiv_symm_of (b : B) :
    (restrictScalarsEquiv B 𝔭).symm (of 𝔭 B b) = of (𝔭.map (algebraMap A B)) B b := by
  ext n
  rfl

end AdicCompletion
