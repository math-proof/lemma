import Mathlib
import Instance.M4aHerbrand_SIdeleClassGroup
import Structure.M4aHerbrand_AdeleBaseChange

set_option autoImplicit false

open NumberField IsDedekindDomain CategoryTheory

noncomputable section

namespace M4aHerbrand

section RepRes

universe u

variable {G G' : Type u} [Group G] [Group G'] {M N : Type u} [CommGroup M] [CommGroup N]
  [MulDistribMulAction G M] [MulDistribMulAction G' N]

end RepRes

namespace AdeleBaseChange

section Maps

variable {R F R' F' : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
  [CommRing R'] [IsDedekindDomain R'] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F']

abbrev idelesMap (B : AdeleBaseChange R F R' F') : (AdeleRing R F)ˣ →* (AdeleRing R' F')ˣ := Units.map B.β.toMonoidHom

end Maps

section Tower

variable {R F R' F' R'' F'' : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
  [CommRing R'] [IsDedekindDomain R'] [Field F'] [Algebra R' F'] [IsFractionRing R' F']
  [CommRing R''] [IsDedekindDomain R''] [Field F''] [Algebra R'' F''] [IsFractionRing R'' F'']
  [Algebra F F'] [Algebra F' F''] [Algebra F F'']
  {T : Set (HeightOneSpectrum R)} {T' : Set (HeightOneSpectrum R')} {T'' : Set (HeightOneSpectrum R'')}

end Tower

section Equivariance

variable {R F R' F' : Type} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]
  [CommRing R'] [IsDedekindDomain R'] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F']
  {L : Type} [Field L] [Algebra L F] [Algebra L F']
  {T : Set (HeightOneSpectrum R)} {T' : Set (HeightOneSpectrum R')}

end Equivariance

end AdeleBaseChange

end M4aHerbrand

end
