module

public import Mathlib
public import Instance.MvFormalGroup_NegV2
public import Instance.MvFormalGroup_CartierModule
public import Theorem.PowerSeries.CartierModuleHomothety

set_option autoImplicit false

@[expose] public noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R]

abbrev cVec {τ : Type} (w : WittVector p R) : WittVector p (MvPolynomial τ R) :=
  WittVector.map (MvPolynomial.C : R →+* MvPolynomial τ R) w

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

namespace Examples

end Examples

end CartierModule

end MvFormalGroup

end
