module
public import Lemma.WeierstrassCurve.FreyPackage
public import Instance.FLTPrelim_GaloisRep
public import Theorem.WeierstrassCurve.FrobeniusTrace
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Instance.FreyPackage_GaloisRep
public import Def.FreyPackage_GaloisRep
set_option autoImplicit false


public section

universe r s v

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]


@[simp]
theorem galoisRep_apply {n : ℕ} (σ : K ≃ₐ[S] K) (P : Submodule.torsionBy ℤ (W'⁄K).Point n) :
    galoisRep W' n σ P = σ • P :=
  rfl

end WeierstrassCurve.Affine.Point
