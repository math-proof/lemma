import Structure.LanglandsTunnell_CubicInduction_Structure
import Instance.LanglandsTunnell_CubicInduction_HeckeRepresentatives

set_option autoImplicit false

open Matrix IsDedekindDomain NumberField

noncomputable section

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives


end LanglandsTunnell.CubicInduction.HeckeRepresentatives

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Hermite

section Transport

open HeckeIntegralSeam HeckePair

variable {G H : Type*} [Group G] [Group H]


end Transport

section ExplicitMatrices

variable {A : Type*} [CommRing A]


end ExplicitMatrices

section DiagonalConjugation

open LanglandsTunnell.CubicInduction

variable {A : Type*} [CommRing A]


end DiagonalConjugation

section DiagonalContinuity

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

omit [IsTopologicalRing A] in


end DiagonalContinuity

section Integral

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]


variable (hinj : Function.Injective (algebraMap R K))
include hinj


end Integral

section Gen1

open LanglandsTunnell.CubicInduction HeckeIntegralSeam HeckePair

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]

private structure IsLocalUniformizer (ϖ : R) : Prop where
  ne_zero : ϖ ≠ 0
  not_isUnit : ¬ IsUnit ϖ
  dvd_of_not_isUnit : ∀ r : R, ¬ IsUnit r → ϖ ∣ r

private structure IsResidueSystem (ϖ : R) {κ : Type} (ℓ : κ → R) : Prop where
  exists_dvd_sub : ∀ r : R, ∃ c : κ, ϖ ∣ r - ℓ c
  eq_of_dvd_sub : ∀ c c' : κ, ϖ ∣ ℓ c - ℓ c' → c = c'


variable (π : Kˣ) {κ : Type} (ℓ : κ → R)


variable {π ℓ}


section Cases

variable {ϖ : R}


end Cases


section Disjoint


end Disjoint


end Gen1

section Gen2

open LanglandsTunnell.CubicInduction HeckeIntegralSeam HeckePair

variable {R K : Type*} [CommRing R] [Field K] [Algebra R K]


end Gen2

section Bridge

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel
open LanglandsTunnell.CubicInduction HeckeIntegralSeam

variable (v : HeightOneSpectrum (𝓞 ℚ))


end Bridge

section Residues

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicHaar
open NumberField.AdelicLevel LanglandsTunnell.CubicInduction HeckeIntegralSeam

variable (v : HeightOneSpectrum (𝓞 ℚ))


end Residues

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Hermite

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Counting

open HeckeIntegralSeam

variable {G : Type*} [Group G]


end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Counting

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Valuations

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

variable (v : HeightOneSpectrum (𝓞 ℚ))


end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Valuations

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Membership

variable (v : HeightOneSpectrum (𝓞 ℚ))
variable {α : Type}

variable {v}


variable (v)


end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Membership

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives.Injectivity


variable {v : HeightOneSpectrum (𝓞 ℚ)} {α : Type}


section Matrices

variable (v)


variable {v}


end Matrices

section Injective

variable {U : Subgroup (LocalGL3 v)}
variable (hU : ∀ k ∈ U, ∀ i j, Valued.v ((k : Mat3 v) i j) ≤ 1)
variable (dig : α → v.adicCompletion ℚ) (hsep : ∀ a b : α, a ≠ b → Valued.v (dig a - dig b) = 1)
variable (hP : Valued.v (ratPrimeUnit v : v.adicCompletion ℚ) < 1) {ϖ : v.adicCompletion ℚ} (hϖ : Valued.v ϖ < 1)
variable (hcorner :
  ((centralGen v * (heckeGen2 v)⁻¹ : LocalGL3 v) : Mat3 v) = !![1, 0, 0; 0, 1, 0; 0, 0, ϖ])


end Injective

end LanglandsTunnell.CubicInduction.HeckeRepresentatives.Injectivity

namespace LanglandsTunnell.CubicInduction.HeckeRepresentatives

section Systems

open HeckeIntegralSeam NumberField.AdelicLevel

variable (v : HeightOneSpectrum (𝓞 ℚ))


end Systems

end LanglandsTunnell.CubicInduction.HeckeRepresentatives

end
