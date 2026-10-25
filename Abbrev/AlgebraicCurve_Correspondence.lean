import Instance.AlgebraicCurve_DivisorPushPull
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section AlongHom

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

abbrev algebraAlong (φ : F →ₐ[K] F') : Algebra F F' := φ.toRingHom.toAlgebra

end AlongHom

namespace Divisor

section AlongHom

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

section Pullback

variable [HasPrincipalDivisors K F'] (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

end Pullback

section Pushforward

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

end Pushforward

end AlongHom

section Correspondence

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)

end Correspondence

end Divisor

namespace Pic0

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)

end Pic0

end AlgebraicCurve

namespace AlgebraicCurve

section AlongPlaces

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

end AlongPlaces

end AlgebraicCurve

namespace AlgebraicCurve

variable {K F F₁ Z : Type*} [Field K] [Field F] [Field F₁] [Field Z]
  [Algebra K F] [Algebra K F₁] [Algebra K Z]

namespace Place

section Fiber

variable [HasPrincipalDivisors K Z]

end Fiber

end Place

end AlgebraicCurve

namespace AlgebraicCurve

section AlongTransport

variable {K F F₁ : Type*} [Field K] [Field F] [Field F₁] [Algebra K F] [Algebra K F₁]

end AlongTransport

end AlgebraicCurve

namespace AlgebraicCurve

namespace SemilinearAut

section Intertwines

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

end Intertwines

end SemilinearAut

end AlgebraicCurve
