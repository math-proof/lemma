import Instance.FLTPrelim_GaloisRep
import Lemma.EllipticCurve.FrobeniusTrace
import Def.EllipticCurve_FrobeniusEndo
import Abbrev.EllipticCurve_FrobeniusEndo

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

noncomputable section

namespace FrobeniusEndo

section Pencil

variable {A : Type*} [AddCommGroup A]


@[simp] lemma linePencil_apply (ψ : A →+ A) (m n : ℤ) (P : A) :
    linePencil ψ m n P = m • P - n • ψ P :=
  rfl


lemma kerDeg_def (ψ : A →+ A) (m n : ℤ) : kerDeg ψ m n = Nat.card (linePencil ψ m n).ker :=
  rfl

lemma mem_ker_linePencil_iff (ψ : A →+ A) (m n : ℤ) (P : A) :
    P ∈ (linePencil ψ m n).ker ↔ m • P = n • ψ P := by
  rw [AddMonoidHom.mem_ker, linePencil_apply, sub_eq_zero]

end Pencil

section Frobenius

variable {R : Type*} {S : Type*} {k : Type*} [CommRing R] [CommRing S] [Field k] [DecidableEq k]
  [Algebra R S] [Algebra R k] [Algebra S k] [IsScalarTower R S k]
  (W : WeierstrassCurve R) (σ : k ≃ₐ[S] k)

lemma frobEnd_apply (P : (W⁄k).Point) : frobEnd W σ P = σ • P :=
  rfl

end Frobenius

end FrobeniusEndo

end
