import Instance.FLTPrelim_GaloisRep
import Instance.EllipticCurve_FrobeniusTrace

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

noncomputable section

namespace FrobeniusEndo

section Pencil

variable {A : Type*} [AddCommGroup A]

def linePencil (ψ : A →+ A) (m n : ℤ) : A →+ A :=
  m • AddMonoidHom.id A - n • ψ


def kerDeg (ψ : A →+ A) (m n : ℤ) : ℕ :=
  Nat.card (linePencil ψ m n).ker

end Pencil

section Frobenius

variable {R : Type*} {S : Type*} {k : Type*} [CommRing R] [CommRing S] [Field k] [DecidableEq k]
  [Algebra R S] [Algebra R k] [Algebra S k] [IsScalarTower R S k]
  (W : WeierstrassCurve R) (σ : k ≃ₐ[S] k)


def FrobCharEqOnPoints (a : ℤ) (q : ℕ) : Prop :=
  ∀ P : (W⁄k).Point, σ • (σ • P) - a • (σ • P) + (q : ℤ) • P = 0

end Frobenius

end FrobeniusEndo

end
