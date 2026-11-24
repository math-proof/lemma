module
public import Mathlib
public import Lemma.LaurentSeries.ArithmeticGalois
public import Theorem.HahnSeries.X0ModL
set_option autoImplicit false


public section

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve

namespace ModularCurve

section Spec

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable {k : Type*} [Field k] (π : A →+* k) (N : ℕ)

def IsPlaceReductionAlong
    (r : Place L (laurentBaseChange L (modularFunctionFieldFull N)) →
      Place k (modularFunctionFieldFullC k N)) : Prop :=
  (∀ P, (r P).deg = P.deg) ∧
    ∀ (y : LaurentSeries A)
      (hy : coeffMap A.subtype y ∈ laurentBaseChange L (modularFunctionFieldFull N))
      (hyk : coeffMap π y ∈ modularFunctionFieldFullC k N),
      coeffMap π y ≠ 0 →
        ∀ D : Divisor L (laurentBaseChange L (modularFunctionFieldFull N)),
          (∀ P, D P = P.ord (⟨coeffMap A.subtype y, hy⟩ : laurentBaseChange L (modularFunctionFieldFull N))) →
            ∀ Q, Finsupp.mapDomain r D Q = Q.ord (⟨coeffMap π y, hyk⟩ : modularFunctionFieldFullC k N)

def integralPrincipalDivisors : Set (Divisor L (laurentBaseChange L (modularFunctionFieldFull N))) :=
  {D | ∃ (y : LaurentSeries A)
      (hy : coeffMap A.subtype y ∈ laurentBaseChange L (modularFunctionFieldFull N)),
      coeffMap π y ∈ modularFunctionFieldFullC k N ∧ coeffMap π y ≠ 0 ∧
        ∀ P, D P = P.ord (⟨coeffMap A.subtype y, hy⟩ : laurentBaseChange L (modularFunctionFieldFull N))}

def PrincipalGeneratedByIntegral : Prop :=
  Divisor.principal (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)) ≤
    AddSubgroup.closure (integralPrincipalDivisors A π N)

def ReductionInputsAlong : Prop :=
  ∃ r, IsPlaceReductionAlong A π N r ∧ PrincipalGeneratedByIntegral A π N

end Spec

section SpecLemmas

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {N : ℕ}
variable {r : Place L (laurentBaseChange L (modularFunctionFieldFull N)) →
  Place k (modularFunctionFieldFullC k N)}

end SpecLemmas

section Descent

variable {L : Type*} [Field L] [Algebra ℚ L] {A : ValuationSubring L}
variable {k : Type*} [Field k] {π : A →+* k} {N : ℕ}
variable (r : Place L (laurentBaseChange L (modularFunctionFieldFull N)) →
  Place k (modularFunctionFieldFullC k N))

def reductionDivAlong :
    Divisor L (laurentBaseChange L (modularFunctionFieldFull N)) →+ Divisor k (modularFunctionFieldFullC k N) :=
  Finsupp.mapDomain.addMonoidHom r

def reductionDegZeroAlong (hdeg : ∀ P, (r P).deg = P.deg) :
    Divisor.degZero (K := L) (F := laurentBaseChange L (modularFunctionFieldFull N)) →+
      Divisor.degZero (K := k) (F := modularFunctionFieldFullC k N) :=
  ((reductionDivAlong r).domRestrict _).codRestrict _ fun D => mapDomain_mem_degZero_of_deg_eq hdeg D.2

def reductionPic0Along (hr : IsPlaceReductionAlong A π N r) (hgen : PrincipalGeneratedByIntegral A π N) :
    Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+ JZeroC k N :=
  QuotientAddGroup.map _ _ (reductionDegZeroAlong r hr.1) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact hr.mapDomain_mem_principal hgen hD)

end Descent

section Total

variable {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L)
variable {k : Type*} [Field k] (π : A →+* k) (N : ℕ)

open Classical in

def reductionAlong : Pic0 L (laurentBaseChange L (modularFunctionFieldFull N)) →+ JZeroC k N :=
  if h : ReductionInputsAlong A π N then reductionPic0Along h.choose h.choose_spec.1 h.choose_spec.2 else 0

variable {A π N}

end Total

section CharL

set_option synthInstance.maxHeartbeats 400000

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (N : ℕ)

abbrev IsPlaceReductionModL
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N)) : Prop :=
  IsPlaceReductionAlong A (IsLocalRing.residue A) N r

abbrev ReductionInputsModL : Prop :=
  ReductionInputsAlong A (IsLocalRing.residue A) N

variable {A N} in

def placeReductionModL (h : ReductionInputsModL A N) :
    Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (IsLocalRing.ResidueField A) (modularFunctionFieldFullC (IsLocalRing.ResidueField A) N) :=
  h.choose

variable {A N} in
abbrev reductionModL : JZero N →+ JZeroC (IsLocalRing.ResidueField A) N :=
  reductionAlong A (IsLocalRing.residue A) N

end CharL


end ModularCurve

end
