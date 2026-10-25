import Structure.HeckeGalois_EichlerShimura
import Abbrev.ModularCurve_EigenformIdeal
import Def.ModularCurve_EichlerShimuraData

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section TateModule

variable (p : ℕ) {G : Type*} [Group G] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction G J] [SMulCommClass G HeckeAlg J]


namespace TateModule

variable {p} {J}


end TateModule


section Bundle

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) [NeZero N] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

structure EichlerShimuraData : Prop where

  freeOfRankTwo : FreeOfRankTwo p J

  unramifiedOutside : UnramifiedOutside (K := K) (L := L) N p J

  frobeniusQuadratic : FrobeniusQuadratic (K := K) (L := L) N p J

  eigenformSupport : EigenformSupport p J (IsEigenformIdeal N)

end Bundle

section Torsion

variable (p : ℕ) {J : Type*} [AddCommGroup J]


variable {p}


end Torsion

section Realization

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J]
variable (k : Type*) [Field k] (φ : HeckeAlg →+* k)
variable (V : Type*) [AddCommGroup V] [Module k V]
variable (π : J → V) (ρ : (L ≃ₐ[K] L) →* (V ≃ₗ[k] V))

structure IsLambdaAdicRealization : Prop where

  finite : Module.Finite k V

  finrank_eq : Module.finrank k V = 2

  map_zero : π 0 = 0

  map_add : ∀ x y : J, IsPPowTorsion p x → IsPPowTorsion p y → π (x + y) = π x + π y

  map_galois : ∀ (σ : L ≃ₐ[K] L) (x : J), IsPPowTorsion p x → π (σ • x) = ρ σ (π x)

  map_hecke : ∀ (t : HeckeAlg) (x : J), IsPPowTorsion p x → π (t • x) = φ t • π x

  spanning : Submodule.span k (π '' {x : J | IsPPowTorsion p x}) = ⊤

namespace IsLambdaAdicRealization

variable {p J k φ V π ρ}
variable (h : IsLambdaAdicRealization p J k φ V π ρ)
include h


end IsLambdaAdicRealization

end Realization

section AttachmentData

variable {k : Type*} [Field k]


end AttachmentData

end ModularCurve

end

end
