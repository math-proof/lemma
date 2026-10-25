import Mathlib
import sympy.Basic
import Lemma.ValuationSubring.ResidueValuationSubring
import Lemma.Int.P2MUtil
open IsLocalRing


/-- ported from external source -/

private lemma  isUnit_iff
  {L : Type*}
  [Field L]
  (A S : ValuationSubring L)
  (h : A ≤ S)
  (a : A) : IsUnit (A.toResidueValuationSubring S h a) ↔ IsUnit a := by
  refine ⟨fun hu => ?_, fun hu => hu.map _⟩
  obtain ⟨b, hb⟩ := A.toResidueValuationSubring_surjective S h
    ((hu.unit⁻¹ : (A.residueValuationSubring S h)ˣ) : A.residueValuationSubring S h)
  have hab : A.toResidueValuationSubring S h (a * b) = 1 := by
    rw [map_mul, hb, IsUnit.mul_val_inv]
  have hmem : a * b - 1 ∈ RingHom.ker (A.toResidueValuationSubring S h) := by
    rw [RingHom.mem_ker, map_sub, hab, map_one, sub_self]
  rw [A.ker_toResidueValuationSubring S h] at hmem
  have hmax : a * b - 1 ∈ maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance) hmem
  have hunit : IsUnit (a * b) := by
    by_contra hnu
    have h1 : a * b ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have : (1 : A) ∈ maximalIdeal A := by
      have := sub_mem h1 hmax
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  refine isUnit_of_mul_isUnit_left hunit

private lemma _root_.CompVUnitSol.valuation_lt_one_iff
  {L : Type*}
  [Field L]
  (A S : ValuationSubring L)
  (h : A ≤ S)
  (a : A) :
  (A.residueValuationSubring S h).valuation (residue S (A.inclusion S h a)) < 1 ↔
    A.valuation (a : L) < 1 := by
  rw [← ValuationSubring.coe_toResidueValuationSubring, ← ValuationSubring.valuation_lt_one_iff,
    ← ValuationSubring.valuation_lt_one_iff, IsLocalRing.mem_maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_iff]
p2m_export "CompVUnitSol" "valuation_lt_one_iff"
@[path]
private lemma main
  [Field L]
  {A S : ValuationSubring L}
  {a : A}
-- given
  (h : A ≤ S) :
-- imply
  (A.residueValuationSubring S h).valuation (IsLocalRing.residue S (A.inclusion S h a)) < 1 ↔
      A.valuation (a : L) < 1 :=
-- proof
  CompVUnitSol.valuation_lt_one_iff A S h a


-- created on 2026-10-23
