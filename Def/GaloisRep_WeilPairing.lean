import Mathlib
import Lemma.FreyPackage.GaloisRep
import Structure.GaloisRep_WeilPairing

set_option autoImplicit false

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

universe r s v

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

variable (S) in


variable (S K) in

def HasWeilPairing (W' : Affine R) (n : ℕ) : Prop :=
  ∃ B : Submodule.torsionBy ℤ (W'⁄K).Point n → Submodule.torsionBy ℤ (W'⁄K).Point n → Kˣ,
    IsWeilPairing S W' n B

end WeierstrassCurve.Affine.Point
