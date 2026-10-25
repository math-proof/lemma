import Mathlib

set_option autoImplicit false

noncomputable section

universe u

open PowerSeries

namespace MvFormalGroup

namespace ArtinHasse

variable (p : ℕ) [hp : Fact p.Prime]

def moebExponent (n : ℕ) : ℤ_[p] :=
  if p ∣ n then 0 else -(ArithmeticFunction.moebius n : ℤ_[p]) * Ring.inverse (n : ℤ_[p])

def moebFactor (n : ℕ) : ℤ_[p]⟦X⟧ :=
  if n = 0 then 1 else (binomialSeries ℤ_[p] (moebExponent p n)).subst (-(X : ℤ_[p]⟦X⟧) ^ n)

def moebProd (k : ℕ) : ℤ_[p]⟦X⟧ :=
  ∏ n ∈ (Finset.Ioc 0 k).filter (fun n => ¬ p ∣ n), moebFactor p n

def series : ℤ_[p]⟦X⟧ :=
  PowerSeries.mk fun k => coeff k (moebProd p k)


variable {A : Type*} [CommRing A] [Algebra ℤ_[p] A]

def scaled (q : ℕ) (z : A) : A⟦X⟧ :=
  PowerSeries.mk fun k => if q ∣ k then algebraMap ℤ_[p] A (coeff (k / q) (series p)) * z ^ (k / q) else 0


def prodSeries (z : ℕ → A) (N : ℕ) : A⟦X⟧ :=
  ∏ m ∈ Finset.range N, scaled p (p ^ m) (z m)


def coord (n : ℕ) : MvPolynomial ℕ ℤ_[p] :=
  coeff (n + 1) (prodSeries p (fun m => (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p])) (n + 1))


variable (R : Type u) [CommRing R] [CharP R p]

def toCharP : ℤ_[p] →+* R := (ZMod.castHom (dvd_refl p) R).comp (PadicInt.toZMod (p := p))

def fam (n : ℕ) : MvPowerSeries ℕ R :=
  ↑(MvPolynomial.map (toCharP p R) (coord p n))

end ArtinHasse

end MvFormalGroup

end
