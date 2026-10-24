import Mathlib
import Lemma.Definitions.Def_Rep_QuotientRightTranslation
import Lemma.Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Lemma.Definitions.Def_ExtEndgame_ProductionDatum
import Lemma.Definitions.Def_Compat_Mathlib430

set_option autoImplicit false

noncomputable section

namespace groupCohomology

open CategoryTheory ExtCitation

abbrev cyclotomicQuotientRep (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime] : Rep (ZMod p) ↥K.fixingSubgroup :=
  (Rep.ofMulActionFinsupp (ZMod p) ↥K.fixingSubgroup (↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)).twist
    ((cycloChar p).comp K.fixingSubgroup.subtype)

variable (S : Finset Nat.Primes) (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (p : ℕ) [Fact p.Prime]
  [(L.fixingSubgroup.subgroupOf K.fixingSubgroup).Normal]

abbrev cyclotomicQuotientRT (c : ↥K.fixingSubgroup) : cyclotomicQuotientRep K L p ⟶ cyclotomicQuotientRep K L p :=
  Rep.quotientRightTranslationTwist (L.fixingSubgroup.subgroupOf K.fixingSubgroup) ((cycloChar p).comp K.fixingSubgroup.subtype)
    (c : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup)

theorem cyclotomicQuotientRT_one : cyclotomicQuotientRT K L p 1 = 𝟙 _ := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  change Finsupp.mapDomain (fun q => q * ((QuotientGroup.mk 1 : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup))⁻¹) x = x
  rw [QuotientGroup.mk_one, inv_one]
  simp only [mul_one]
  exact Finsupp.mapDomain_id

theorem cyclotomicQuotientRT_of_mem (c : ↥K.fixingSubgroup) (hc : (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup) :
    cyclotomicQuotientRT K L p c = 𝟙 _ := by
  have h1 : (c : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) = 1 :=
    (QuotientGroup.eq_one_iff c).2 (Subgroup.mem_subgroupOf.2 hc)
  have h2 : (c : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) = ((1 : ↥K.fixingSubgroup) : _ ⧸ _) := by
    rw [h1, QuotientGroup.mk_one]
  change Rep.quotientRightTranslationTwist _ _ (c : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup) = _
  rw [h2]
  exact cyclotomicQuotientRT_one K L p

theorem cyclotomicQuotientRT_mul (c c' : ↥K.fixingSubgroup) :
    cyclotomicQuotientRT K L p (c * c') = cyclotomicQuotientRT K L p c' ≫ cyclotomicQuotientRT K L p c := by
  apply Rep.hom_ext
  refine DFunLike.ext _ _ fun x => ?_
  change Finsupp.mapDomain (fun q => q * ((QuotientGroup.mk (c * c') : ↥K.fixingSubgroup ⧸ L.fixingSubgroup.subgroupOf K.fixingSubgroup))⁻¹) x =
    Finsupp.mapDomain (fun q => q * ((QuotientGroup.mk c : _ ⧸ _))⁻¹) (Finsupp.mapDomain (fun q => q * ((QuotientGroup.mk c' : _ ⧸ _))⁻¹) x)
  rw [← Finsupp.mapDomain_comp]
  congr 1
  ext q
  simp only [Function.comp_apply, QuotientGroup.mk_mul, mul_inv_rev, mul_assoc]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

def cyclotomicQuotientH2ρ : Representation (ZMod p) ↥K.fixingSubgroup (continuousH2Sr K.fixingSubgroup.subtype S (cyclotomicQuotientRep K L p)) where
  toFun c := continuousH2SrMapHom S K.fixingSubgroup.subtype (cyclotomicQuotientRT K L p c)
  map_one' := (congrArg (continuousH2SrMapHom S K.fixingSubgroup.subtype (A := cyclotomicQuotientRep K L p) (B := cyclotomicQuotientRep K L p))
      (cyclotomicQuotientRT_one K L p)).trans (continuousH2SrMapHom_id S K.fixingSubgroup.subtype (A := cyclotomicQuotientRep K L p))
  map_mul' c c' := (congrArg (continuousH2SrMapHom S K.fixingSubgroup.subtype (A := cyclotomicQuotientRep K L p) (B := cyclotomicQuotientRep K L p))
      (cyclotomicQuotientRT_mul K L p c c')).trans (continuousH2SrMapHom_comp S K.fixingSubgroup.subtype _ _)

set_option synthInstance.maxHeartbeats 400000 in

def cyclotomicQuotientH2Rep : Rep (ZMod p) ↥K.fixingSubgroup := Rep.of (cyclotomicQuotientH2ρ S K L p)

set_option synthInstance.maxHeartbeats 400000 in
theorem cyclotomicQuotientH2Rep_ρ_apply (c : ↥K.fixingSubgroup) (x : cyclotomicQuotientH2Rep S K L p) :
    (cyclotomicQuotientH2Rep S K L p).ρ c x = continuousH2SrMapHom S K.fixingSubgroup.subtype (cyclotomicQuotientRT K L p c) x := rfl

set_option synthInstance.maxHeartbeats 400000 in

theorem cyclotomicQuotientH2Rep_ρ_eq_one_of_mem (c : ↥K.fixingSubgroup) (hc : (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) ∈ L.fixingSubgroup) :
    (cyclotomicQuotientH2Rep S K L p).ρ c = 1 :=
  (congrArg (continuousH2SrMapHom S K.fixingSubgroup.subtype (A := cyclotomicQuotientRep K L p) (B := cyclotomicQuotientRep K L p))
      (cyclotomicQuotientRT_of_mem K L p c hc)).trans (continuousH2SrMapHom_id S K.fixingSubgroup.subtype (A := cyclotomicQuotientRep K L p))

end groupCohomology

end
