import Mathlib
import Def.AlgebraicCurve_RegularDifferentials
import Lemma.AlgebraicCurve.GluedPic0

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

private def unifLDR : F :=
  ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)


def HasPoleOrderLE (n : ℕ) (ω : Ω[F⁄K]) : Prop :=
  ∃ f : F, v.unifLDR ^ n * f ∈ v.toValuationSubring ∧ ω = f • v.dCoord


variable {v}

variable (v) in


end Place

section LogForms

variable (K F)


variable {K F}


end LogForms

namespace LogDeRham

variable (K F)


namespace H1

variable {K F}
variable (S : Set (Place K F))


end H1

section Map

variable {K F}
variable {F' : Type*} [Field F'] [Algebra K F']


end Map

section Frobenius

variable {K F}
variable (p : ℕ) [Fact p.Prime] [CharP K p]

omit [Fact p.Prime] in


variable (S : Set (Place K F))


end Frobenius

section Cartier

variable {K F}
variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

structure CartierHypotheses (C : Ω[F⁄K] →+ Ω[F⁄K]) : Prop where
  semi : ∀ (a : K) (ω : Ω[F⁄K]), C (a • ω) = (frobeniusEquiv K p).symm a • C ω
  ker : ∀ f : F, C (D K F f) = 0
  regular : ∀ (v : Place K F) (ω : Ω[F⁄K]), v.HasPoleOrderLE 0 ω → v.HasPoleOrderLE 0 (C ω)
  log : ∀ (v : Place K F) (ω : Ω[F⁄K]), v.HasPoleOrderLE 1 ω → v.HasPoleOrderLE 1 (C ω)

variable {p}
variable {C : Ω[F⁄K] →+ Ω[F⁄K]} (hC : CartierHypotheses p C)
variable (S : Set (Place K F))


end Cartier

end LogDeRham

end AlgebraicCurve

end
