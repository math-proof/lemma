import Lemma.Definitions.Def_FLTPrelim_GaloisRep
import Lemma.Definitions.Def_EllipticCurve_FrobeniusTrace

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

noncomputable section

namespace FrobeniusEndo

section Pencil

variable {A : Type*} [AddCommGroup A]

def linePencil (ψ : A →+ A) (m n : ℤ) : A →+ A :=
  m • AddMonoidHom.id A - n • ψ

@[simp] lemma linePencil_apply (ψ : A →+ A) (m n : ℤ) (P : A) :
    linePencil ψ m n P = m • P - n • ψ P :=
  rfl

def kerDeg (ψ : A →+ A) (m n : ℤ) : ℕ :=
  Nat.card (linePencil ψ m n).ker

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

abbrev frobEnd : (W⁄k).Point →+ (W⁄k).Point :=
  DistribSMul.toAddMonoidHom (W⁄k).Point σ

lemma frobEnd_apply (P : (W⁄k).Point) : frobEnd W σ P = σ • P :=
  rfl

abbrev frobPencilEnd (p : ℕ) (m n : ℤ) :
    Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄k).Point p) :=
  ((m : ZMod p) • (1 : Module.End (ZMod p) (Submodule.torsionBy ℤ (W⁄k).Point p))) -
    (n : ZMod p) • galoisRepModuleEnd S W p σ

def FrobCharEqOnPoints (a : ℤ) (q : ℕ) : Prop :=
  ∀ P : (W⁄k).Point, σ • (σ • P) - a • (σ • P) + (q : ℤ) • P = 0

end Frobenius

end FrobeniusEndo

end
