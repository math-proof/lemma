import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

set_option autoImplicit false

noncomputable section

open Module

namespace ModularCurve

namespace MazurII142

namespace OdaDictionaryNoBT1

section Derived

variable {𝕋 : Type*} [CommRing 𝕋] {J : Type*} [AddCommGroup J] [Module 𝕋 J] {𝔪 : Ideal 𝕋}
  {k : Type*} [Field k]
  {Vrep : Type*} [AddCommGroup Vrep] [Module (𝕋 ⧸ 𝔪) Vrep]
  {HDR : Type*} [AddCommGroup HDR] [Module k HDR]
  {MV : Type*} [AddCommGroup MV] [Module k MV]
  {H0Ω : Type*} [AddCommGroup H0Ω] [Module k H0Ω]
  {H1O : Type*} [AddCommGroup H1O] [Module k H1O]

-- OdaDictionaryNoBT1.kernelPair lives in Structure.HeckeGalois_MazurCase1BundleNoBT1.

end Derived

end OdaDictionaryNoBT1

universe u v

attribute [local instance] Ideal.Quotient.field

end MazurII142

end ModularCurve

end
