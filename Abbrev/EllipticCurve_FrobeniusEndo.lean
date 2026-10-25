import Instance.FLTPrelim_GaloisRep
import Instance.EllipticCurve_FrobeniusTrace

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

noncomputable section

namespace FrobeniusEndo

section Pencil

variable {A : Type*} [AddCommGroup A]


end Pencil

section Frobenius

variable {R : Type*} {S : Type*} {k : Type*} [CommRing R] [CommRing S] [Field k] [DecidableEq k]
  [Algebra R S] [Algebra R k] [Algebra S k] [IsScalarTower R S k]
  (W : WeierstrassCurve R) (σ : k ≃ₐ[S] k)

abbrev frobEnd : (W⁄k).Point →+ (W⁄k).Point :=
  DistribSMul.toAddMonoidHom (W⁄k).Point σ

abbrev frobPencilEnd (p : ℕ) (m n : ℤ) :
    Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄k).Point p) :=
  ((m : ZMod p) • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄k).Point p))) -
    (n : ZMod p) • galoisRepModuleEnd S W p σ

end Frobenius

end FrobeniusEndo

end
