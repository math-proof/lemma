module
public import Mathlib
public import Def.FormalGroup_CartierModule
public import Def.PowerSeries_CartierModuleHomothety
public import Def.FormalGroup_CartierModuleWittAction
public import Def.FormalGroup_CartierModuleIntVerschiebung
public import Def.CerednikDrinfeld_SpecialFormalModule
public import Theorem.FormalGroup.CartierGradedPiece
public import Def.CerednikDrinfeld_GradedCartierModuleData
set_option autoImplicit false


public section

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries

namespace WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {R : Type u} [CommRing R]

omit hp in

end WittLaw


end MvFormalGroup

namespace CerednikDrinfeld

namespace FormalODModule

open MvFormalGroup MvPowerSeries.CartierModule MvPowerSeries PowerSeries MvPolynomial

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

def varpiLinear (X : FormalODModule p B) :
    CartierModule p X.F →ₗ[WittVector p B] CartierModule p X.F where
  toFun := endAct X.varpiEnd
  map_add' := map_add (endAct X.varpiEnd)
  map_smul' := endAct_smul_witt X.varpiEnd

def gradedSubmodule (X : FormalODModule p B) (j : Zp2 p →+* B) (n : ℕ) :
    Submodule (WittVector p B) (CartierModule p X.F) where
  carrier := X.gradedPiece j n
  add_mem' hf hg := (X.gradedPiece j n).add_mem hf hg
  zero_mem' := (X.gradedPiece j n).zero_mem
  smul_mem' w {f} hf := smul_mem_gradedPiece X j n w f hf

def toGradedCartierModuleData {B : Type} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1)) : GradedCartierModuleData p B j where
  M := CartierModule p X.F
  frobenius := MvPowerSeries.CartierModule.frobenius
  verschiebung := MvFormalGroup.CartierModule.verschiebungInt
  varpi := X.varpiLinear
  piece i := X.gradedSubmodule j (i : ℕ)
  frobenius_smul := frobenius_smul
  smul_verschiebung := smul_verschiebungInt
  verschiebung_smul_frobenius := verschiebungInt_smul_frobenius
  frobenius_verschiebung := frobenius_verschiebungInt
  varpi_verschiebung := endAct_verschiebungInt X.varpiEnd
  varpi_frobenius := endAct_frobenius X.varpiEnd
  varpi_varpi := endAct_varpiEnd_endAct_varpiEnd X
  isCompl_piece := (isCompl_gradedSubmodule_iff X j 0 1).2 hc
  verschiebung_mem i f hf := by
    show verschiebungInt f ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ)
    rw [gradedPiece_fin_add_one]
    exact verschiebungInt_mem_gradedPiece_succ X j i f hf
  frobenius_mem i f hf := by
    show MvPowerSeries.CartierModule.frobenius f ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ)
    rw [gradedPiece_fin_add_one]
    exact frobenius_mem_gradedPiece_succ X j i f hf
  varpi_mem i f hf := by
    show endAct X.varpiEnd f ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ)
    rw [gradedPiece_fin_add_one]
    exact endAct_varpiEnd_mem_gradedPiece_succ X j i f hf

section model

variable {B : Type} [CommRing B] (X : FormalODModule p B) (j : Zp2 p →+* B)
  (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))

end model

end FormalODModule

end CerednikDrinfeld

end
