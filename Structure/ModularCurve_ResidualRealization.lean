import Structure.HeckeGalois_EichlerShimura
import Def.FLTPrelim_Ramification
import Instance.EllipticCurve_FrobeniusTrace
import Mathlib.LinearAlgebra.Determinant
import Def.ModularCurve_ResidualRealization

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section ResidualRealization

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]
variable (k : Type*) [Field k] (φ : HeckeAlg →+* k)
variable (V : Type*) [AddCommGroup V] [Module k V]
variable (π : J → V) (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V))

structure IsResidualRealization : Prop where

  finite : Module.Finite k V

  finrank_eq : Module.finrank k V = 2

  map_zero : π 0 = 0

  map_add : ∀ x y : J, p • x = 0 → p • y = 0 → π (x + y) = π x + π y

  map_galois : ∀ (σ : L ≃ₐ[K] L) (x : J), p • x = 0 → π (σ • x) = ρ σ (π x)

  map_hecke : ∀ (t : HeckeAlg) (x : J), p • x = 0 → π (t • x) = φ t • π x

  spanning : Submodule.span k (π '' {x : J | p • x = 0}) = ⊤

end ResidualRealization

end ModularCurve

end
