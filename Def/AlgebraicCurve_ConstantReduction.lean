module

public import Mathlib
public import Def.AlgebraicCurve_DivisorClassGroup
public import Theorem.Submodule.Repartitions
public import Structure.AlgebraicCurve_ConstantReduction

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

open IsLocalRing

variable {L : Type*} [Field L] (A : ValuationSubring L)
variable (F : Type*) [Field F] [Algebra L F]
variable (Fbar : Type*) [Field Fbar] [Algebra (ResidueField A) Fbar]


namespace ConstantReduction

variable {A F Fbar}

set_option linter.unusedVariables false in

def IsGood (R : ConstantReduction A F Fbar) : Prop :=
  genusFF (ResidueField A) Fbar = genusFF L F

variable (R : ConstantReduction A F Fbar)

def divMap : Divisor L F →+ Divisor (ResidueField A) Fbar :=
  Finsupp.mapDomain.addMonoidHom R.placeMap

def degZeroMap :
    Divisor.degZero (K := L) (F := F) →+ Divisor.degZero (K := ResidueField A) (F := Fbar) :=
  (R.divMap.domRestrict (Divisor.degZero (K := L) (F := F))).codRestrict _ fun D => R.mapDomain_mem_degZero D.2

def pic0Map : Pic0 L F →+ Pic0 (ResidueField A) Fbar :=
  QuotientAddGroup.map _ _ R.degZeroMap (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact R.mapDomain_mem_principal hD)

end ConstantReduction

end AlgebraicCurve

end

end
