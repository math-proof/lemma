import Mathlib
import Def.FormalGroup_NegV2
import Def.FormalGroup_CartierModule
import Def.PowerSeries_CartierModuleHomothety
import Def.FormalGroup_CartierModuleWittAction

set_option autoImplicit false

noncomputable section

universe u


namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] (R : Type u) [CommRing R]

def xTaut : WittVector p (MvPolynomial ℕ R) :=
  WittVector.mk p (MvPolynomial.X : ℕ → MvPolynomial ℕ R)

def frobPoly (n : ℕ) : MvPolynomial ℕ R := (WittVector.frobenius (xTaut p R)).coeff n

def frobPolyFam : ℕ → MvPowerSeries ℕ R := fun n => (frobPoly p R n : MvPowerSeries ℕ R)

variable {p R}

omit hp in
def curvePoly (R : Type u) [CommRing R] : ℕ → MvPolynomial Unit R
  | 0 => MvPolynomial.X ()
  | _ + 1 => 0

omit hp in
end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

def verschiebungInt [Φ.IsComm] : CartierModule p Φ →+ CartierModule p Φ :=
  precomp WittLaw.isEndo_frobPolyFam


end CartierModule

end MvFormalGroup

end
