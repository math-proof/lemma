import Lemma.FLTPrelim.FreyPackage
import Instance.FLTPrelim_GaloisRep
import Lemma.EllipticCurve.FrobeniusTrace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Instance.FreyPackage_GaloisRep
import Def.FreyPackage_GaloisRep

set_option autoImplicit false

universe r s v

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]


@[simp]
lemma galoisRep_apply {n : ℕ} (σ : K ≃ₐ[S] K) (P : Submodule.torsionBy ℤ (W'⁄K).Point n) :
    galoisRep W' n σ P = σ • P :=
  rfl

end WeierstrassCurve.Affine.Point
