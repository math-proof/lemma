import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule
import Lemma.MvFormalGroup.CartierModuleHomothety
import Instance.MvFormalGroup_CartierModuleWittAction
import Instance.MvFormalGroup_WittPointFamily

set_option autoImplicit false

noncomputable section

universe u v w

namespace MvFormalGroup

open MvPowerSeries WittLaw

structure SeriesPoint {d : ℕ} {R : Type u} [CommRing R] (Φ : MvFormalGroup d R) (τ : Type v) :
    Type (max u v) where

  val : Fin d → MvPowerSeries τ R

  constantCoeff_eq_zero : ∀ j, (val j).constantCoeff = 0

namespace SeriesPoint

variable {d d' : ℕ} {R : Type u} [CommRing R] {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}
  {τ : Type v} {τ' : Type w}


end SeriesPoint

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R] {τ : Type v} {τ' : Type w}


variable {p}

omit hp [CommRing R] in


variable (p R τ)


variable {p R τ}


end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {τ : Type v} {τ' : Type w}


namespace Examples


end Examples

end CartierModule

end MvFormalGroup

end
