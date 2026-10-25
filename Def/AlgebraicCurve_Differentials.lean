import Class.AlgebraicCurve_DivisorClassGroup
import Mathlib.RingTheory.Kaehler.Basic

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

open Classical in

def uniformizer_alt : F :=
  if h : ∃ t : F, v.ord t = 1 then h.choose else 0


def diffCoeff (t : F) (ω : Ω[F⁄K]) : F :=
  if h : ∃ g : F, ω = g • D K F t then h.choose else 0


def ordDiff (ω : Ω[F⁄K]) : ℤ :=
  v.ord (diffCoeff v.uniformizer_alt ω)


end Place

variable (K F) in

def IsRegularDiff (ω : Ω[F⁄K]) : Prop :=
  ∀ v : Place K F, 0 ≤ v.ordDiff ω


def regularDiffs : Submodule K Ω[F⁄K] :=
  Submodule.span K {ω : Ω[F⁄K] | IsRegularDiff K F ω}


section Pullback

variable {F' : Type*} [Field F'] [Algebra K F']

def pullbackDiff (φ : F →ₐ[K] F') : Ω[F⁄K] →ₗ[K] Ω[F'⁄K] :=
  letI : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  (KaehlerDifferential.map K K F F').restrictScalars K


end Pullback

end AlgebraicCurve

end
