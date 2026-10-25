import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule
import Lemma.MvFormalGroup.CartierModuleHomothety
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Def.CerednikDrinfeld_CartierGradedPiece

set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld

variable {p : ℕ} [hp : Fact p.Prime]


namespace FormalODModule

open MvFormalGroup MvFormalGroup.CartierModule SpecialFormal

variable {B : Type u} [CommRing B] {B' : Type v} [CommRing B']

def frobTwist (X : FormalODModule p B) : FormalODModule p B where
  F := X.F
  isComm := X.isComm
  act a := X.act (WittVector.frobenius a)
  varpi := X.varpi
  isLawHom_act a := X.isLawHom_act _
  isLawHom_varpi := X.isLawHom_varpi
  act_one := by rw [map_one, X.act_one]
  act_mul a b := by rw [map_mul, X.act_mul]
  act_add a b := by rw [map_add, X.act_add]
  varpi_comp_varpi := by rw [X.varpi_comp_varpi, map_natCast]
  varpi_comp_act a := X.varpi_comp_act _

end FormalODModule

end CerednikDrinfeld

end
