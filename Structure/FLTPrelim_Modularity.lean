import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.ArithmeticSubgroups
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike
import Mathlib.Util.CompileInductive
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

universe u

namespace ModularFormClass

def qCoeff (f : ℍ → ℂ) (n : ℕ) : ℂ :=
  (qExpansion 1 f).coeff n

end ModularFormClass

namespace CuspForm

open ModularFormClass

structure IsNormalizedEigenform {N : ℕ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    Prop where

  qCoeff_one : qCoeff f 1 = 1

  qCoeff_mul_of_coprime : ∀ m n : ℕ, m.Coprime n →
    qCoeff f (m * n) = qCoeff f m * qCoeff f n

  qCoeff_prime_pow_of_not_dvd : ∀ p r : ℕ, p.Prime → ¬ p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1)) - p * qCoeff f (p ^ r)

  qCoeff_prime_pow_of_dvd : ∀ p r : ℕ, p.Prime → p ∣ N →
    qCoeff f (p ^ (r + 2)) = qCoeff f p * qCoeff f (p ^ (r + 1))

end CuspForm

namespace WeierstrassCurve

namespace Affine

variable {R : Type u} [CommRing R] {W' : Affine R}


end Affine

section Card

variable {F : Type u} [CommRing F] (W : WeierstrassCurve F)


end Card


open CuspForm


end WeierstrassCurve

end
