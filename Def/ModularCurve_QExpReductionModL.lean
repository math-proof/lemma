module

public import Mathlib
public import Def.ModularCurve_X1

@[expose] public section

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve

namespace ModularCurve

section Spec

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable {k : Type*} [Field k] (π : A →+* k)
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (Fbar : IntermediateField k (LaurentSeries k))

def IsLaurentPlaceReduction (r : Place L (laurentBaseChange L F₀) → Place k Fbar) : Prop :=
  (∀ P, (r P).deg = P.deg) ∧
    ∀ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ laurentBaseChange L F₀)
      (hyk : coeffMap π y ∈ Fbar), coeffMap π y ≠ 0 →
        ∀ D : Divisor L (laurentBaseChange L F₀),
          (∀ P, D P = P.ord (⟨coeffMap A.subtype y, hy⟩ : laurentBaseChange L F₀)) →
            ∀ Q, Finsupp.mapDomain r D Q = Q.ord (⟨coeffMap π y, hyk⟩ : Fbar)

def laurentIntegralPrincipalDivisors : Set (Divisor L (laurentBaseChange L F₀)) :=
  {D | ∃ (y : LaurentSeries A) (hy : coeffMap A.subtype y ∈ laurentBaseChange L F₀),
      coeffMap π y ∈ Fbar ∧ coeffMap π y ≠ 0 ∧
        ∀ P, D P = P.ord (⟨coeffMap A.subtype y, hy⟩ : laurentBaseChange L F₀)}

def LaurentPrincipalGeneratedByIntegral : Prop :=
  Divisor.principal (K := L) (F := laurentBaseChange L F₀) ≤
    AddSubgroup.closure (laurentIntegralPrincipalDivisors A π F₀ Fbar)

def LaurentReductionInputs : Prop :=
  ∃ r, IsLaurentPlaceReduction A π F₀ Fbar r ∧ LaurentPrincipalGeneratedByIntegral A π F₀ Fbar

end Spec


section Descent

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k}
variable {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} {Fbar : IntermediateField k (LaurentSeries k)}
variable (r : Place L (laurentBaseChange L F₀) → Place k Fbar)

def laurentReductionDiv : Divisor L (laurentBaseChange L F₀) →+ Divisor k Fbar :=
  Finsupp.mapDomain.addMonoidHom r

def laurentReductionDegZero (hdeg : ∀ P, (r P).deg = P.deg) :
    Divisor.degZero (K := L) (F := laurentBaseChange L F₀) →+ Divisor.degZero (K := k) (F := Fbar) :=
  ((laurentReductionDiv r).domRestrict _).codRestrict _
    fun D => mapDomain_mem_degZero_of_laurent_deg_eq hdeg D.2

def laurentReductionPic0 (hr : IsLaurentPlaceReduction A π F₀ Fbar r)
    (hgen : LaurentPrincipalGeneratedByIntegral A π F₀ Fbar) :
    Pic0 L (laurentBaseChange L F₀) →+ Pic0 k Fbar :=
  QuotientAddGroup.map _ _ (laurentReductionDegZero r hr.1) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact hr.mapDomain_mem_principal hgen hD)

end Descent

section Total

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable {k : Type*} [Field k] (π : A →+* k)
variable (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) (Fbar : IntermediateField k (LaurentSeries k))

open Classical in

def laurentReduction : Pic0 L (laurentBaseChange L F₀) →+ Pic0 k Fbar :=
  if h : LaurentReductionInputs A π F₀ Fbar then
    laurentReductionPic0 h.choose h.choose_spec.1 h.choose_spec.2
  else 0

variable {A π F₀ Fbar}

end Total


section CharL

set_option synthInstance.maxHeartbeats 400000

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

abbrev IsPlaceReductionQExpModL
    (r : Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) →
      Place (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)) : Prop :=
  IsLaurentPlaceReduction A (IsLocalRing.residue A) (qExpFunctionFieldC ℚ Γ)
    (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) r

abbrev ReductionInputsQExpModL : Prop :=
  LaurentReductionInputs A (IsLocalRing.residue A) (qExpFunctionFieldC ℚ Γ)
    (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)

variable {A Γ} in

def placeReductionQExpModL (h : ReductionInputsQExpModL A Γ) :
    Place (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) →
      Place (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :=
  h.choose

variable {A Γ} in
abbrev reductionQExpModL :
    Pic0 (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)) →+
      Pic0 (IsLocalRing.ResidueField A) (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ) :=
  laurentReduction A (IsLocalRing.residue A) (qExpFunctionFieldC ℚ Γ)
    (qExpFunctionFieldC (IsLocalRing.ResidueField A) Γ)

end CharL

end ModularCurve

end
