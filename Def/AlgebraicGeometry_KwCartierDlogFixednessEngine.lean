import Mathlib
import Lemma.AlgebraicGeometry.KwCartierOperatorTCoordEngine
import Lemma.ModularCurve.KwNo6HspecCartierDlogCampaignFrame

open Polynomial AlgebraicCurve.KwPke AlgebraicCurve.KwCart

noncomputable section

namespace AlgebraicCurve.KwCfx


section GenericModel

variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

def kw_cfx_G : Polynomial (MvPolynomial (Fin ℓ) ℤ) :=
  ∑ i : Fin ℓ, C (MvPolynomial.X i) * X ^ (i : ℕ)

def kw_cfx_Gpow : Polynomial (MvPolynomial (Fin ℓ) ℤ) :=
  ∑ i : Fin ℓ, C (MvPolynomial.X i ^ ℓ) * X ^ (ℓ * (i : ℕ))

end GenericModel

section Transport

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [hℓ : Fact ℓ.Prime] [CharP F ℓ]

def kw_cfx_tau (t : F) : kw_pke_pthPowers F ℓ :=
  ⟨t ^ ℓ, (kw_pke_mem_pthPowers_iff F ℓ).mpr ⟨t, rfl⟩⟩


def kw_cfx_vext (v : Fin ℓ → kw_pke_pthPowers F ℓ) (n : ℕ) :
    kw_pke_pthPowers F ℓ :=
  if h : n < ℓ then v ⟨n, h⟩ else 0


def kw_cfx_phiP (v : Fin ℓ → kw_pke_pthPowers F ℓ) :
    MvPolynomial (Fin ℓ) ℤ →+* kw_pke_pthPowers F ℓ :=
  (MvPolynomial.aeval v).toRingHom


def kw_cfx_phi (v : Fin ℓ → kw_pke_pthPowers F ℓ) :
    MvPolynomial (Fin ℓ) ℤ →+* F :=
  ((kw_pke_pthPowers F ℓ).subtype).comp (kw_cfx_phiP v)


def kw_cfx_Phi (t : F) (v : Fin ℓ → kw_pke_pthPowers F ℓ) :
    Polynomial (MvPolynomial (Fin ℓ) ℤ) →+* F :=
  Polynomial.eval₂RingHom (kw_cfx_phi v) t


def kw_cfx_fstarOf (t : F) (v : Fin ℓ → kw_pke_pthPowers F ℓ) : F :=
  ∑ i : Fin ℓ, ((i : ℕ) : F) * ((v i : F)) * t ^ ((i : ℕ) - 1)

end Transport

end AlgebraicCurve.KwCfx

end
