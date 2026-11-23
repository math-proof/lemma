module

public import Mathlib
public import Def.ExtCitation_KummerBridge
public import Abbrev.Compat_Mathlib430
public import Abbrev.GroupCohomology_Selmer
public import Abbrev.Rep_QuotientRightTranslation

set_option autoImplicit false

@[expose] public noncomputable section

namespace groupCohomology

open CategoryTheory ExtCitation

abbrev cyclotomicQuotientRep (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime] :
    Rep (ZMod p) ↥K.fixingSubgroup :=
  (Rep.ofMulActionFinsupp (ZMod p) ↥K.fixingSubgroup
      (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)).twist
    ((cycloChar p).comp K.fixingSubgroup.subtype)

variable (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime]
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal]

abbrev cyclotomicQuotientRT (c : ↥K.fixingSubgroup) :
    cyclotomicQuotientRep K L p ⟶ cyclotomicQuotientRep K L p :=
  Rep.quotientRightTranslationTwist (L.fixingSubgroup.subgroupOf K.fixingSubgroup)
    ((cycloChar p).comp K.fixingSubgroup.subtype)
    (c : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)

end groupCohomology

end
