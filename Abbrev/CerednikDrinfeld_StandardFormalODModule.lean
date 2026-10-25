import Mathlib
import Instance.MvFormalGroup_NegV2
import Structure.CerednikDrinfeld_SpecialFormalModule
import Instance.CerednikDrinfeld_LubinTateModule

section BoxBasisLemmaAppendix

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u

noncomputable section

open MvPowerSeries

namespace CerednikDrinfeld.BoxBasisLemma

variable {R : Type*} [CommRing R] {g : ℕ} {N : Fin g → ℕ}

abbrev powIdeal (R : Type*) [CommRing R] (g : ℕ) (N : Fin g → ℕ) : Ideal (MvPowerSeries (Fin g) R) :=
  Ideal.span (Set.range fun i : Fin g => (X i : MvPowerSeries (Fin g) R) ^ N i)

end CerednikDrinfeld.BoxBasisLemma

end

end BoxBasisLemmaAppendix

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.LubinTate

namespace CerednikDrinfeld.Standard

universe u v

variable {p : ℕ} [Fact p.Prime]

local notation "𝕆" => Zp2 p
local notation "𝔮" => Fintype.card (GaloisField p 2)

section Standard

end Standard

section Identities

end Identities

section OverB

variable {B : Type*} [CommRing B] [CharP B p] (j : Zp2 p →+* B)

end OverB

section HomAlgebra

variable {R : Type*} [CommRing R] {g h k m : ℕ}

end HomAlgebra

section Biproduct

variable {B : Type u} [CommRing B] [CharP B p] (j : Zp2 p →+* B)

end Biproduct

end CerednikDrinfeld.Standard

end
