import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open scoped TensorProduct

namespace NeronModelInfra.TopFormOrder

variable (R' K' O F : Type u) [CommRing R'] [CommRing K'] [Algebra R' K']
  [CommRing O] [Algebra R' O] [CommRing F] [Algebra O F] [Algebra K' F] [Algebra R' F]
  [IsScalarTower R' O F] [IsScalarTower R' K' F] (d : ℕ)

@[reducible] def moduleAlong (N : Type u) [AddCommGroup N] [Module F N] : Module O N :=
  Module.compHom N (algebraMap O F)

set_option backward.isDefEq.respectTransparency false in
def ιMultiAlong :
    letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
    (Ω[O⁄R']) [⋀^Fin d]→ₗ[O] (⋀[F]^d (Ω[F⁄K'])) :=
  letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
  haveI : IsScalarTower O F (⋀[F]^d (Ω[F⁄K'])) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  { ((exteriorPower.ιMulti F d (M := Ω[F⁄K'])).toMultilinearMap.restrictScalars O).compLinearMap
      (fun _ => KaehlerDifferential.map R' K' O F) with
    map_eq_zero_of_eq' := fun v i j h hij =>
      (exteriorPower.ιMulti F d (M := Ω[F⁄K'])).map_eq_zero_of_eq _ (by simp [h]) hij }

def topFormMap :
    letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
    ⋀[O]^d (Ω[O⁄R']) →ₗ[O] ⋀[F]^d (Ω[F⁄K']) :=
  letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
  exteriorPower.alternatingMapLinearEquiv (ιMultiAlong R' K' O F d)

def integralTopForms :
    letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
    Submodule O (⋀[F]^d (Ω[F⁄K'])) :=
  letI := moduleAlong O F (⋀[F]^d (Ω[F⁄K']))
  LinearMap.range (topFormMap R' K' O F d)

section Order

variable [IsDomain O] [IsDiscreteValuationRing O]
variable (L : Type u) [Field L] [Algebra O L] [IsFractionRing O L] [Algebra K' L] [Algebra R' L]
  [IsScalarTower R' O L] [IsScalarTower R' K' L]

open IsDedekindDomain IsLocalRing in

def maximalSpectrum : HeightOneSpectrum O :=
  ⟨maximalIdeal O, inferInstance, IsDiscreteValuationRing.not_a_field O⟩

open IsDedekindDomain in

def addOrd (a : L) : ℤ :=
  open scoped Classical in
  if h : a = 0 then 0
  else -(Multiplicative.toAdd (WithZero.unzero
    (((maximalSpectrum O).valuation L).ne_zero_iff.mpr h)))

def ord (ω : ⋀[L]^d (Ω[L⁄K'])) : ℤ :=
  open scoped Classical in
  letI := moduleAlong O L (⋀[L]^d (Ω[L⁄K']))
  if h : ∃ ρ : ⋀[L]^d (Ω[L⁄K']), integralTopForms R' K' O L d = Submodule.span O {ρ} ∧ ∃ a : L, ω = a • ρ
  then addOrd O L (a := h.choose_spec.2.choose)
  else 0

end Order

end NeronModelInfra.TopFormOrder

end
