import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep

set_option autoImplicit false

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

variable (S K) in

def HasGaloisStableCofixedLine (W' : Affine R) (n : ℕ) : Prop :=
  ∃ N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n),
    IsGaloisStable S N ∧ N ≠ ⊥ ∧ N ≠ ⊤ ∧
      ∀ σ : K ≃ₐ[S] K, ∀ x : Submodule.torsionBy ℤ (W'⁄K).Point n, σ • x - x ∈ N

end WeierstrassCurve.Affine.Point
