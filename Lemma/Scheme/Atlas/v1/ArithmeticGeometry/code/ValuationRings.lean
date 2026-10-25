import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.ValuationRings.Part4
open Ideal Submodule
open IsLocalRing Module


/--
[valuationRing_isLocal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
lemma valuationRing_isLocal
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [ValuationRing R] :
-- imply
  IsLocalRing R :=
-- proof
  inferInstance
section Lemma1619

/--
[ValuationRing.ideal_le_or_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
lemma ValuationRing.ideal_le_or_le
  [CommRing R]
  [IsDomain R]
  [ValuationRing R]
  {𝔞 𝔟 : Ideal R} :
-- imply
  𝔞 ≤ 𝔟 ∨ 𝔟 ≤ 𝔞 :=
-- proof
  (ValuationRing.iff_ideal_total.mp ‹_›).total 𝔞 𝔟
end Lemma1619

/--
[ValuationRing.fg_isPrincipal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
lemma ValuationRing.fg_isPrincipal
  [CommRing R]
  [IsDomain R]
  [ValuationRing R]
  {I : Ideal R}
-- given
  (hI : I.FG) :
-- imply
  I.IsPrincipal :=
-- proof
  IsBezout.isPrincipal_of_FG I hI
section Lemma1622

/--
[valuationRing_iff_of_localRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
lemma valuationRing_iff_of_localRing
  {R : Type*}
  [CommRing R]
  [IsDomain R]
  [IsLocalRing R] :
-- imply
  (ValuationRing R ∧ ¬IsField R) ↔ (¬IsField R ∧ IsBezout R) := by
-- proof
  constructor
  ·
    rintro ⟨_, hNF⟩
    exact ⟨hNF, inferInstance⟩
  ·
    rintro ⟨hNF, _⟩
    exact ⟨inferInstance, hNF⟩
end Lemma1622
section LocalRing

/--
[localRing_iff_unique_maximal_ideal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
lemma localRing_iff_unique_maximal_ideal
  {R : Type*}
  [CommSemiring R] :
-- imply
  IsLocalRing R ↔ ∃! I : Ideal R, I.IsMaximal := by
-- proof
  constructor
  · intro _
    exact IsLocalRing.maximal_ideal_unique R
  · exact IsLocalRing.of_unique_max_ideal

/--
[isLocalRing_iff_nonunits_isIdeal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
lemma isLocalRing_iff_nonunits_isIdeal
  {R : Type*}
  [CommRing R] :
-- imply
  IsLocalRing R ↔ ∃ I : Ideal R, (I : Set R) = nonunits R := by
-- proof
  constructor
  ·
    intro hR
    exact ⟨IsLocalRing.maximalIdeal R, Set.ext fun x =>
      (IsLocalRing.mem_maximalIdeal x).symm⟩
  ·
    rintro ⟨I, hI⟩
    haveI : Nontrivial R := by
      by_contra h
      rw [not_nontrivial_iff_subsingleton] at h
      have h0 : (0 : R) ∈ nonunits R := hI ▸ I.zero_mem
      have : (0 : R) = 1 := @Subsingleton.elim R h 0 1
      exact h0 (this ▸ isUnit_one)
    apply IsLocalRing.of_nonunits_add
    intro a b ha hb
    rw [← hI] at ha hb ⊢
    exact I.add_mem ha hb

/--
[regularLocalRing_dim_one_iff_dvr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
lemma regularLocalRing_dim_one_iff_dvr
  {R : Type*}
  [CommRing R]
  [IsDomain R] :
-- imply
  (IsRegularLocalRing R ∧ ringKrullDim R = 1) ↔ IsDiscreteValuationRing R := by
-- proof
  constructor
  · rintro ⟨hreg, hdim⟩
    haveI := hreg.toIsLocalRing
    haveI : IsNoetherianRing R := inferInstance
    rw [← finrank_CotangentSpace_eq_one_iff]
    have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp hreg
    exact_mod_cast hfin.trans hdim
  · intro hdvr
    refine ⟨inferInstance, ?_⟩
    exact IsPrincipalIdealRing.ringKrullDim_eq_one R
      (isField_iff_maximalIdeal_eq.not.mpr (IsDiscreteValuationRing.not_a_field R))
section DVR_Noetherian

/--
[valuationRing_noetherian_iff_dvr](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
lemma valuationRing_noetherian_iff_dvr
  {R : Type*}
  [CommRing R]
  [IsDomain R]
-- given
  (hR : ¬IsField R) :
-- imply
  (ValuationRing R ∧ IsNoetherianRing R) ↔ IsDiscreteValuationRing R := by
-- proof
  constructor
  · rintro ⟨hV, hN⟩
    haveI := hV
    haveI := hN
    exact ((IsDiscreteValuationRing.TFAE R hR).out 1 0).mp hV
  · intro hdvr
    exact ⟨inferInstance, inferInstance⟩
end DVR_Noetherian
section LocalizationAtPrime

/--
[localizationAtPrime.maximalIdeal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
lemma localizationAtPrime.maximalIdeal_eq
  {R : Type*}
  [CommRing R]
  {𝔭 : Ideal R}
  [𝔭.IsPrime] :
-- imply
  IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) = 𝔭.map (algebraMap R (Localization.AtPrime 𝔭)) :=
-- proof
  (Localization.AtPrime.map_eq_maximalIdeal).symm

/--
[valuation_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
lemma valuation_mul
  [CommRing R]
  [IsDomain R]
  [ValuationRing R]
  [Field K]
  [Algebra R K]
  [IsFractionRing R K]
  {x y : K} :
-- imply
  ValuationRing.valuation R K (x * y) = ValuationRing.valuation R K x * ValuationRing.valuation R K y :=
-- proof
  map_mul _ x y

/--
[maximalIdealAtPoint_isMaximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
lemma maximalIdealAtPoint_isMaximal
  [CommRing R]
  [Field k]
  {φ : R →+* k}
-- given
  (hφ : Function.Surjective φ) :
-- imply
  (maximalIdealAtPoint φ).IsMaximal :=
-- proof
  RingHom.ker_isMaximal_of_surjective φ hφ

/--
[isValuationSubring_iff_forall_units](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ValuationRings.lean)
-/
@[path]
private lemma isValuationSubring_iff_forall_units_eq
  [Field K]
  {R : Subring K} :
-- imply
  (∀ x : K, x ∈ R ∨ x⁻¹ ∈ R) ↔ (∀ x : K, x ≠ 0 → (x ∈ R ∨ x⁻¹ ∈ R)) := by
-- proof
  apply isValuationSubring_iff_forall_units R


-- created on 2026-10-23
