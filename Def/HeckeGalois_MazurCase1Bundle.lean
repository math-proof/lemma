import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Quotient.Basic

set_option autoImplicit false

noncomputable section

open Module

namespace ModularCurve

namespace MazurII142

section Carrier

variable (k : Type*) [Field k] (M : Type*) [AddCommGroup M] [Module k M]

end Carrier

namespace VerFrobPair

section Basic

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]

-- ver_frob_apply / frob_ver_apply live in Structure.HeckeGalois_MazurCase1Bundle
-- (FontaineLayer / Def to Structure import direction).

end Basic

section Duality

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]

end Duality

section StableQuotient

variable {k : Type*} [Field k] {M : Type*} [AddCommGroup M] [Module k M]

-- Stable / quotientPair live in Structure.HeckeGalois_MazurCase1Bundle.

end StableQuotient

section Kernel

variable {k : Type*} [Field k] {M₂ M₃ : Type*}
  [AddCommGroup M₂] [Module k M₂] [AddCommGroup M₃] [Module k M₃]

-- kernelPair lives in Structure.HeckeGalois_MazurCase1Bundle.

end Kernel

end VerFrobPair

namespace OdaDictionary

section Derived

variable {𝕋 : Type*} [CommRing 𝕋] {J : Type*} [AddCommGroup J] [Module 𝕋 J] {𝔪 : Ideal 𝕋}
  {k : Type*} [Field k]
  {Vrep : Type*} [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
  {HDR : Type*} [AddCommGroup HDR] [Module k HDR]
  {MV : Type*} [AddCommGroup MV] [Module k MV]
  {H0Ω : Type*} [AddCommGroup H0Ω] [Module k H0Ω]
  {H1O : Type*} [AddCommGroup H1O] [Module k H1O]

-- OdaDictionary.kernelPair lives in Structure.HeckeGalois_MazurCase1Bundle.

end Derived

end OdaDictionary

universe u v

attribute [local instance] Ideal.Quotient.field

end MazurII142

end ModularCurve

end
